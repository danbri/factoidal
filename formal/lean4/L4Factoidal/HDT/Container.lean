/-
L4Factoidal.HDT.Container — HDT v1 container reader.

Port of `formal/fstar/HDT.Container.fst` (644 lines). Stage 1 of the
HDT program plan: parse the container skeleton of an HDT v1 file as
written by hdt-cpp 1.3.x — the Global control information (`$HDT`
cookie, format IRI, properties, CRC16), the Header section (control
information + N-Triples metadata text), the Dictionary control
information plus the byte boundaries of its four Plain-Front-Coding
sections, and the Triples control information. Every control block's
CRC16 is checked here.

Byte-layout provenance: rdfhdt.org "HDT binary format" draft
(03/07/2015), cross-checked against the vendored hdt-cpp-1.3.3 sources
(`third_party/testing/hdt/README.md`). Where they disagree, hdt-cpp
wins.

## Three F* pieces are absent, and why

The F* module carries machinery that exists only to work around its
I/O boundary. None of it has a job in Lean.

1. `hdt_file_size` (exponential probe + binary search, 128 lines with
   its two helpers). The F* tree reads bytes through
   `Parquet.Footer.parquet_read_range_hex`, which does not report a
   file size, so the size is DISCOVERED by probing read lengths. Lean
   has `IO.FS.readBinFile : FilePath → IO ByteArray`, and `.size` is
   a field. The probe has nothing to find.
2. `hdt_bytes_of_hex` and `collect_bytes`. The F* boundary hands back
   a hex STRING, which must be decoded to bytes before anything can
   index it. `readBinFile` gives a `ByteArray` directly.
3. `nat_xor` (bitwise XOR built out of `/`, `%` and `*` over unbounded
   naturals). It exists because `FStar.UInt32`'s stdint externals have
   no js_of_ocaml realisation. `UInt16.xor` is a Lean primitive.

Those three are about a fifth of the F* module. The container parsing
below is ported rule for rule.

## One deliberate difference: header text decoding

`bytes_to_string_acc` in F* maps each byte through
`Parser.NTriples.safe_char_of_int` — one character per byte, Latin-1
style. In OCaml that reproduces the file's bytes exactly, because an
OCaml string IS a byte string. A Lean `String` is UTF-8, so the same
per-byte mapping would re-encode every byte above 0x7F as two bytes
and corrupt UTF-8 header metadata. `bytesToString` below decodes the
range as UTF-8 first and falls back to the per-byte mapping only when
the range is not valid UTF-8. On ASCII input — every control block —
the two agree byte for byte.
-/
import L4Factoidal.RDF.Graph
import L4Factoidal.Syntax.NTriples

namespace L4Factoidal.HDT

open L4Factoidal.RDF

/-! ## Bytes

`ByteArray` replaces the F* `FStar.ImmutableArray.Base.t` of refined
naturals: O(1) indexing, O(1) size, and it is what `IO.FS.readBinFile`
returns. -/

abbrev Bytes := ByteArray

/-- Byte at `i`, or `none` past the end. Port of `byte_get`. -/
def byteAt (a : Bytes) (i : Nat) : Option UInt8 :=
  if h : i < a.size then some a[i] else none

/-- The same, as a `Nat`, for the arithmetic the format is written in. -/
def byteNat (a : Bytes) (i : Nat) : Option Nat :=
  (byteAt a i).map UInt8.toNat

/-! ## CRC-16/ANSI ("ARC")

Poly 0x8005 reflected (0xA001), init 0x0000, xorout 0x0000 — the
parameters in hdt-cpp's `crc16.h`, used for every control-information
block. Bitwise reflected form; blocks are tens of bytes, so no table. -/

/-- One bit of the reflected CRC-16 register. Port of `crc16_step`. -/
def crc16Step (c : UInt16) : UInt16 :=
  if c &&& 1 == 1 then (c >>> 1) ^^^ 0xA001 else c >>> 1

/-- Eight bits, i.e. one input byte. Port of `crc16_byte`. -/
def crc16Byte (crc : UInt16) (b : UInt8) : UInt16 :=
  let c0 := crc ^^^ b.toUInt16
  crc16Step (crc16Step (crc16Step (crc16Step
    (crc16Step (crc16Step (crc16Step (crc16Step c0)))))))

/-- CRC16 over `[pos, pos+count)`. `none` if the range runs off the
    end. Port of `crc16_range`. -/
def crc16Range (a : Bytes) (pos count : Nat) (crc : UInt16) : Option UInt16 :=
  match count with
  | 0 => some crc
  | n + 1 =>
      match byteAt a pos with
      | none   => none
      | some b => crc16Range a (pos + 1) n (crc16Byte crc b)

/-! ## VByte, HDT flavour

hdt-cpp `libdcs/VByte.cpp`: little-endian 7-bit groups, continuation
bytes with the high bit CLEAR and the FINAL byte with the high bit
SET. That is the inverse of the protobuf/Parquet varint convention,
so a varint reader borrowed from `Parquet.Footer` reads HDT files
wrong rather than failing on them. -/

/-- Port of `vbyte_decode_acc`. Returns `(value, offset-after)`. -/
def vbyteDecodeAcc (a : Bytes) (pos fuel mult acc : Nat) : Option (Nat × Nat) :=
  match fuel with
  | 0 => none
  | f + 1 =>
      match byteNat a pos with
      | none   => none
      | some b =>
          if b ≥ 128 then some (acc + (b - 128) * mult, pos + 1)
          else vbyteDecodeAcc a (pos + 1) f (mult * 128) (acc + b * mult)

/-- Ten 7-bit groups cover any u64. Port of `vbyte_decode`. -/
def vbyteDecode (a : Bytes) (pos : Nat) : Option (Nat × Nat) :=
  vbyteDecodeAcc a pos 10 1 0

/-! ## Small utilities over bytes -/

/-- Offset of the next NUL at or after `pos`, fuel-bounded. Port of
    `scan_nul`. -/
def scanNul (a : Bytes) (pos fuel : Nat) : Option Nat :=
  match fuel with
  | 0 => none
  | f + 1 =>
      match byteNat a pos with
      | none   => none
      | some 0 => some pos
      | some _ => scanNul a (pos + 1) f

/-- Per-byte fallback decoding, one character per byte (Latin-1). -/
def bytesToStringLatin1 (a : Bytes) (pos count : Nat) : Option String :=
  let rec go (i n : Nat) (acc : List Char) : Option String :=
    match n with
    | 0 => some (String.ofList acc.reverse)
    | m + 1 =>
        match byteNat a i with
        | none   => none
        | some b => go (i + 1) m (Char.ofNat b :: acc)
  go pos count []

/-- Decode `[pos, pos+count)` as text. UTF-8 first (see the module
    header on why this differs from `bytes_to_string`), per-byte
    otherwise. Port of `bytes_to_string`. -/
def bytesToString (a : Bytes) (pos count : Nat) : Option String :=
  if pos + count > a.size then none
  else
    let slice := (List.range count).map (fun i => a[pos + i]!)
    match String.fromUTF8? ⟨slice.toArray⟩ with
    | some s => some s
    | none   => bytesToStringLatin1 a pos count

/-! ## Properties

A control block's property field is `"k1=v1;k2=v2;"`. Ports of
`split_on_semi`, `split_on_eq`, `kv_of_chars`, `parse_properties`. -/

def splitOnSemi : List Char → List Char → List (List Char)
  | [],      cur => match cur with | [] => [] | _ => [cur.reverse]
  | c :: rest, cur =>
      if c == ';' then cur.reverse :: splitOnSemi rest []
      else splitOnSemi rest (c :: cur)

def splitOnEq : List Char → List Char → (List Char × List Char)
  | [],        acc => (acc.reverse, [])
  | c :: rest, acc =>
      if c == '=' then (acc.reverse, rest) else splitOnEq rest (c :: acc)

def kvOfChars (p : List Char) : String × String :=
  let (k, v) := splitOnEq p []
  (String.ofList k, String.ofList v)

def parseProperties (raw : String) : List (String × String) :=
  (splitOnSemi raw.toList []).map kvOfChars

def propLookup (props : List (String × String)) (key : String) : Option String :=
  match props.find? (fun kv => kv.1 == key) with
  | some (_, v) => some v
  | none        => none

def natOfDigits : List Char → Nat → Option Nat
  | [],        acc => some acc
  | c :: rest, acc =>
      let d := c.toNat
      if d ≥ 48 && d ≤ 57 then natOfDigits rest (acc * 10 + (d - 48)) else none

def natOfString (s : String) : Option Nat :=
  match s.toList with
  | []  => none
  | cs  => natOfDigits cs 0

def propNat (props : List (String × String)) (key : String) : Option Nat :=
  (propLookup props key).bind natOfString

/-! ## Control information blocks

    '$HDT'(4) type(1) format NUL properties NUL crc16(2 LE)

with the CRC16 taken over cookie..second-NUL inclusive
(`ControlInformation::save`/`load` in hdt-cpp). -/

inductive CIType where
  | unknown | global | header | dictionary | triples | index
  deriving Repr, DecidableEq, Inhabited

def ciTypeOfByte (b : Nat) : CIType :=
  match b with
  | 1 => .global
  | 2 => .header
  | 3 => .dictionary
  | 4 => .triples
  | 5 => .index
  | _ => .unknown

structure ControlInfo where
  start      : Nat                       -- byte offset of '$HDT'
  ciType     : CIType
  format     : String                    -- format URI / name (no NUL)
  props      : List (String × String)
  propsRaw   : String
  crcStored  : UInt16
  crcComputed : UInt16
  crcOk      : Bool
  «end»      : Nat                       -- offset just past the CRC16
  deriving Repr, Inhabited

/-- Port of `parse_control_info`. Rejects a block whose leading four
    bytes are not `$HDT` before it decodes anything else. -/
def parseControlInfo (a : Bytes) (pos : Nat) : Option ControlInfo := do
  let b0 ← byteNat a pos
  let b1 ← byteNat a (pos + 1)
  let b2 ← byteNat a (pos + 2)
  let b3 ← byteNat a (pos + 3)
  if !(b0 == 0x24 && b1 == 0x48 && b2 == 0x44 && b3 == 0x54) then none
  else do
    let ty ← byteNat a (pos + 4)
    let fmtNul ← scanNul a (pos + 5) a.size
    let propsNul ← scanNul a (fmtNul + 1) a.size
    let fmt ← bytesToString a (pos + 5) (fmtNul - (pos + 5))
    let raw ← bytesToString a (fmtNul + 1) (propsNul - (fmtNul + 1))
    let crc ← crc16Range a pos (propsNul + 1 - pos) 0
    let lo ← byteNat a (propsNul + 1)
    let hi ← byteNat a (propsNul + 2)
    let stored : UInt16 := UInt16.ofNat (lo + 256 * hi)
    some {
      start := pos, ciType := ciTypeOfByte ty, format := fmt,
      props := parseProperties raw, propsRaw := raw,
      crcStored := stored, crcComputed := crc, crcOk := crc == stored,
      «end» := propsNul + 3 }

/-! ## Section skippers

Stage 1 computes byte boundaries only, from the self-describing
preambles. Payload decode is stage 2/3.

Log-array (hdt-cpp `LogSequence2::save`):
`type(1)=1 numbits(1) vbyte(numentries) crc8(1) data[⌈numbits·numentries/8⌉] crc32(4)`

Bitmap (hdt-cpp `BitSequence375::save`):
`type(1)=1 vbyte(numbits) crc8(1) data[bits=0 ? 1 : ⌈numbits/8⌉] crc32(4)`
— note the 1-byte floor for the empty bitmap.

PFC dictionary section (hdt-cpp `CSD_PFC::save`; type byte 2 = PFC,
ONE byte, not the spec page's u32):
`type(1)=2 vbyte(numstrings) vbyte(packed-bytes) vbyte(blocksize) crc8(1) log-array crc32(4)` -/

structure LogArrayInfo where
  start      : Nat
  numbits    : Nat
  numentries : Nat
  dataStart  : Nat
  dataBytes  : Nat
  «end»      : Nat
  deriving Repr, Inhabited

def parseLogArrayInfo (a : Bytes) (pos : Nat) : Option LogArrayInfo := do
  let ty ← byteNat a pos
  if ty != 1 then none
  else do
    let numbits ← byteNat a (pos + 1)
    let (numentries, pCrc8) ← vbyteDecode a (pos + 2)
    let dataStart := pCrc8 + 1
    let dataBytes := (numbits * numentries + 7) / 8
    some { start := pos, numbits := numbits, numentries := numentries,
           dataStart := dataStart, dataBytes := dataBytes,
           «end» := dataStart + dataBytes + 4 }

structure BitmapInfo where
  start     : Nat
  numbits   : Nat
  dataStart : Nat
  dataBytes : Nat
  «end»     : Nat
  deriving Repr, Inhabited

def parseBitmapInfo (a : Bytes) (pos : Nat) : Option BitmapInfo := do
  let ty ← byteNat a pos
  if ty != 1 then none
  else do
    let (numbits, pCrc8) ← vbyteDecode a (pos + 1)
    let dataStart := pCrc8 + 1
    let dataBytes := if numbits == 0 then 1 else ((numbits - 1) / 8) + 1
    some { start := pos, numbits := numbits, dataStart := dataStart,
           dataBytes := dataBytes, «end» := dataStart + dataBytes + 4 }

/-- The F* field `pfc_type : (t:nat{t = 2})` is a refinement whose only
    inhabitant is 2. Lean carries no such field: a `PfcSection` value
    exists only where `parsePfcSection` read a type byte of 2, so the
    field would record a constant. When stage 2 widens the accepted
    type bytes, the discriminant becomes real information and gets a
    field then. -/
structure PfcSection where
  start       : Nat
  numstrings  : Nat
  packedBytes : Nat
  blocksize   : Nat
  blocks      : LogArrayInfo            -- block-start offsets
  packedStart : Nat
  «end»       : Nat
  deriving Repr, Inhabited

def parsePfcSection (a : Bytes) (pos : Nat) : Option PfcSection := do
  let ty ← byteNat a pos
  if ty != 2 then none
  else do
    let (numstrings, p1) ← vbyteDecode a (pos + 1)
    let (packedBytes, p2) ← vbyteDecode a p1
    let (blocksize, p3) ← vbyteDecode a p2
    -- p3 points at the CRC8 of the preamble; blocks follow it.
    let la ← parseLogArrayInfo a (p3 + 1)
    some { start := pos, numstrings := numstrings, packedBytes := packedBytes,
           blocksize := blocksize, blocks := la, packedStart := la.end,
           «end» := la.end + packedBytes + 4 }

/-! ## Whole-container inventory -/

structure Inventory where
  global          : ControlInfo
  headerCi        : ControlInfo
  headerDataStart : Nat
  headerDataLen   : Nat
  dictCi          : ControlInfo
  dictShared      : PfcSection
  dictSubjects    : PfcSection
  dictPredicates  : PfcSection
  dictObjects     : PfcSection
  triplesCi       : ControlInfo
  triplesDataStart : Nat
  deriving Repr, Inhabited

/-- Parse the container skeleton from offset 0. `none` on: wrong
    cookie, wrong section type byte, any control-block CRC16 mismatch,
    missing header `length` property, non-PFC dictionary section type
    (stage 2 will widen), or truncation. Port of
    `hdt_parse_inventory_hex`. -/
def parseInventory (a : Bytes) : Option Inventory := do
  let g ← parseControlInfo a 0
  if !(g.ciType == .global && g.crcOk) then none
  else do
    let h ← parseControlInfo a g.end
    if !(h.ciType == .header && h.crcOk) then none
    else do
      let hlen ← propNat h.props "length"
      let hdata := h.end
      let d ← parseControlInfo a (hdata + hlen)
      if !(d.ciType == .dictionary && d.crcOk) then none
      else do
        let secSh ← parsePfcSection a d.end
        let secSu ← parsePfcSection a secSh.end
        let secPr ← parsePfcSection a secSu.end
        let secOb ← parsePfcSection a secPr.end
        let t ← parseControlInfo a secOb.end
        if !(t.ciType == .triples && t.crcOk) then none
        else some {
          global := g, headerCi := h,
          headerDataStart := hdata, headerDataLen := hlen,
          dictCi := d, dictShared := secSh, dictSubjects := secSu,
          dictPredicates := secPr, dictObjects := secOb,
          triplesCi := t, triplesDataStart := t.end }

/-- Header metadata as text. Port of `hdt_header_text_hex`. -/
def headerText (a : Bytes) (inv : Inventory) : Option String :=
  bytesToString a inv.headerDataStart inv.headerDataLen

/-- Header metadata through the verified N-Triples parser. Port of
    `hdt_header_triples_hex`. The F* original calls
    `Parser.NTriples.parse_ntriples`, whose OCaml realisation returns a
    triple list and drops parse errors; the Lean parser returns
    `Except`, so the error is carried here rather than erased. -/
def headerTriples (a : Bytes) (inv : Inventory) : Option (Except String Graph) :=
  (headerText a inv).map (fun text =>
    match Syntax.parseNTriples text with
    | .ok g    => .ok g
    | .error e => .error (toString (repr e)))

/-- Declared triples order (1 = SPO). Port of `hdt_triples_order`. -/
def triplesOrder (inv : Inventory) : Option Nat :=
  propNat inv.triplesCi.props "order"

/-! ## File entry point

The F* module needs `hdt_file_size`, `hdt_read_file_hex` and
`hdt_bytes_of_hex` between the path and the bytes. Here the whole
chain is `readBinFile`. -/

/-- Read a file and parse its container skeleton. Port of
    `hdt_read_inventory`. Returns the bytes as well, so stage-2
    lookups decode further sections without re-reading. -/
def readInventory (path : System.FilePath) : IO (Option (Bytes × Inventory)) := do
  if !(← path.pathExists) then return none
  let a ← IO.FS.readBinFile path
  return (parseInventory a).map (fun inv => (a, inv))

/-! ## Build-time checks

### CRC-16/ARC against its published check value

Every CRC catalogue entry carries a "check" field: the CRC of the nine
ASCII bytes `123456789`. For CRC-16/ARC that value is 0xBB3D. This
checks the parameters, not just the code's self-consistency. -/

def crcOfString (s : String) : Option UInt16 :=
  let bs : Bytes := ⟨s.toUTF8.data⟩
  crc16Range bs 0 bs.size 0

#guard crcOfString "123456789" == some 0xBB3D
#guard crcOfString "" == some 0

/-! ### VByte, HDT flavour

300 encodes as `2C 82`: low group 44 with the high bit CLEAR, final
group 2 with the high bit SET. A protobuf-flavour reader gets this
wrong instead of failing on it, which is why the case is here. -/

def bytesOf (l : List UInt8) : Bytes := ⟨l.toArray⟩

#guard vbyteDecode (bytesOf [0x82]) 0 == some (2, 1)
#guard vbyteDecode (bytesOf [0x2C, 0x82]) 0 == some (300, 2)
#guard vbyteDecode (bytesOf [0x80]) 0 == some (0, 1)
#guard vbyteDecode (bytesOf [0x2C]) 0 == none      -- truncated: no final byte
#guard vbyteDecode (bytesOf []) 0 == none

/-! ### Properties -/

#guard parseProperties "a=1;b=2;" == [("a", "1"), ("b", "2")]
#guard propNat (parseProperties "length=42;order=1;") "length" == some 42
#guard propNat (parseProperties "length=x;") "length" == none
#guard propLookup (parseProperties "a=1;") "b" == none

/-! ### A whole Global control-information block

Built here rather than sliced out of a fixture, so the check states
the layout: `$HDT`, type byte 1, format `<f>` NUL, properties NUL,
then the CRC16 little-endian over everything before it. -/

def ciBody : List UInt8 :=
  [0x24, 0x48, 0x44, 0x54,              -- "$HDT"
   0x01,                                 -- type = Global
   0x3C, 0x66, 0x3E, 0x00,               -- "<f>" NUL
   0x61, 0x3D, 0x31, 0x3B, 0x00]         -- "a=1;" NUL

def ciBlock : Bytes :=
  let body := bytesOf ciBody
  match crc16Range body 0 body.size 0 with
  | none     => body
  | some crc => bytesOf (ciBody ++ [(crc &&& 0xFF).toUInt8, (crc >>> 8).toUInt8])

#guard (parseControlInfo ciBlock 0).map (·.ciType) == some .global
#guard (parseControlInfo ciBlock 0).map (·.crcOk) == some true
#guard (parseControlInfo ciBlock 0).map (·.format) == some "<f>"
#guard (parseControlInfo ciBlock 0).map (·.props) == some [("a", "1")]
#guard (parseControlInfo ciBlock 0).map (·.end) == some 16

/-! ### Corruption is refused, not reinterpreted

The F* module proves this as two lemmas
(`lemma_parse_control_info_rejects_bad_cookie` and
`lemma_bad_global_cookie_rejects_container`). Both hold by unfolding —
`parseControlInfo` tests the four cookie bytes before it touches
anything else, and `parseInventory` forwards that `none`. The Lean
statements are in `L4Factoidal/HDT/ContainerTheorems.lean`; the checks
here are the executable witnesses. -/

def ciBlockBadCookie : Bytes :=
  bytesOf ((0x25 :: ciBody.tail) ++ [0x00, 0x00])

#guard (parseControlInfo ciBlockBadCookie 0).isNone
#guard (parseInventory ciBlockBadCookie).isNone
#guard (parseInventory (bytesOf [])).isNone

/-! A correct cookie with a wrong CRC is refused at the inventory
    level, which is where the check lives. -/

#guard (parseControlInfo (bytesOf (ciBody ++ [0x00, 0x00])) 0).map (·.crcOk) == some false
#guard (parseInventory (bytesOf (ciBody ++ [0x00, 0x00]))).isNone

end L4Factoidal.HDT
