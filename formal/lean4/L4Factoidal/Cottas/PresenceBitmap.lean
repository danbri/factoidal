/-
L4Factoidal.Cottas.PresenceBitmap — the per-row-group presence companion.

Port of `formal/fstar/RDF.CottasStore.PresenceBitmap.fst` (257 lines),
together with the parts of `RDF.CottasStore.OnDiskIndex.fst` that decide
what the `.presence` bytes MEAN.

The columnar store writes, beside each column, a `.presence` companion
recording which row groups contain which dictionary tokens. A query that
binds a term can then skip whole row groups. The prune is an
optimisation, so its correctness contract is one-sided: a `false` must
mean "no row here", while a `true` may be wrong in the safe direction.

## The file format

```
[ magic      : u32 LE   ASCII 'COTP' = 0x50544F43 ]
[ version    : u32 LE   layout version, currently 1 ]
[ numRgs     : u32 LE ]
[ numTokens  : u32 LE ]
[ bitmap     : ⌈numRgs · numTokens / 8⌉ bytes, row-major.
               Bit (rg · numTokens + tok) is set iff row group `rg`
               contains a row with that token. LSB-first within a byte. ]
```

## Where the ten `assume val`s went

`RDF.CottasStore.OnDiskIndex.fst` declares TEN `assume val` I/O
primitives — `mmap_companion_open`, `read_companion_u32_le`,
`read_companion_byte`, and so on — and every read in the F\* presence
module goes through them. The OCaml glue mmaps the companion at boot and
serves byte ranges.

None of them has a Lean counterpart, for the same reason the HDT
container's file-size probe and hex decode have none: `IO.FS.readBinFile`
returns a `ByteArray`, and every definition below is a pure function of
that array. Reading the file happens once, at the edge, in
`openBitmap`. So the Lean tree's realisation surface for this module is
EMPTY where the F\* tree's is ten declarations plus their glue.

## The safe-direction defaults, which are the whole contract

The F\* module is careful about which way each failure falls, and the
port keeps every one:

| Situation | Answer | Why |
|---|---|---|
| `rg` or `tok` out of range | `false` | there is no such row group, so nothing is skipped wrongly |
| byte read off the end | `true` | over-include: the caller scans the row group, finds nothing, and the result set is unchanged |
| companion did not open | `true` | same |
| header invalid | `true` | same |
| column unbound in the pattern | `true` | every row group is a candidate for a wildcard |

Note the asymmetry: an out-of-range INDEX answers `false` while an
out-of-range READ answers `true`. They are different situations. An
index past `numTokens` is a caller contract violation — a token id that
no dictionary produced — and reporting `false` for it is correct,
because no row can hold a token that does not exist. A read past the end
of the buffer means the FILE is short, which says nothing about the
data, so the only safe answer is to include.
-/

namespace L4Factoidal.Cottas

/-! ## The header -/

def cotpMagicU32 : UInt32 := 0x50544F43
def cotdMagicU32 : UInt32 := 0x44544F43
def layoutVersion : UInt32 := 1
def presenceHeaderSize : Nat := 16

structure PresenceHeader where
  magic     : UInt32
  version   : UInt32
  numRgs    : Nat
  numTokens : Nat
  deriving Repr, DecidableEq, Inhabited

def PresenceHeader.ok (h : PresenceHeader) : Bool :=
  h.magic == cotpMagicU32 && h.version == layoutVersion

def readU32Le (bs : ByteArray) (off : Nat) : Option UInt32 :=
  if off + 4 > bs.size then none
  else
    some (bs[off]!.toUInt32 ||| (bs[off+1]!.toUInt32 <<< 8) |||
          (bs[off+2]!.toUInt32 <<< 16) ||| (bs[off+3]!.toUInt32 <<< 24))

def readPresenceHeader (bs : ByteArray) : Option PresenceHeader := do
  let magic ← readU32Le bs 0
  let version ← readU32Le bs 4
  let numRgs ← readU32Le bs 8
  let numTokens ← readU32Le bs 12
  some { magic := magic, version := version,
         numRgs := numRgs.toNat, numTokens := numTokens.toNat }

/-! ## The handle -/

/-- An opened companion: its bytes and its parsed header. The F\* handle
    carries the PATH, because every read goes back through the mmap
    primitives. Here it carries the bytes, read once. -/
structure BitmapHandle where
  bytes  : ByteArray
  header : PresenceHeader

def BitmapHandle.ok (h : BitmapHandle) : Bool := h.header.ok

/-- Parse an already-read companion. `none` unless the header parses AND
    its magic and version match the layout this module knows how to
    read — a caller falls back to "include every row group", which is
    the safe under-prune. -/
def openBitmapBytes (bs : ByteArray) : Option BitmapHandle :=
  match readPresenceHeader bs with
  | none   => none
  | some h => if h.ok then some { bytes := bs, header := h } else none

/-- Read a companion file. The only `IO` in the module. -/
def openBitmap (path : System.FilePath) : IO (Option BitmapHandle) := do
  if !(← path.pathExists) then return none
  return openBitmapBytes (← IO.FS.readBinFile path)

/-! ## The lookup primitive

One byte read and one bit test. See the module header's table for why
each failure falls the way it does. -/

def presenceTestBit (bs : ByteArray) (h : PresenceHeader) (rg tok : Nat) : Bool :=
  if rg ≥ h.numRgs || tok ≥ h.numTokens then false
  else
    let bitIndex := rg * h.numTokens + tok
    let off := presenceHeaderSize + bitIndex / 8
    if off ≥ bs.size then true          -- short file: over-include
    else (bs[off]!.toNat / (2 ^ (bitIndex % 8))) % 2 == 1

def rgContainsToken (h : BitmapHandle) (rg tok : Nat) : Bool :=
  presenceTestBit h.bytes h.header rg tok

/-- The shape a prune call site wants: a possibly-absent handle and a
    possibly-unbound column, with the over-include fallbacks built in. -/
def rgCouldContain (oh : Option BitmapHandle) (rg : Nat) (boundTokId : Option Nat) : Bool :=
  match boundTokId with
  | none     => true                    -- unbound column: every rg is a candidate
  | some tok =>
      match oh with
      | none   => true                  -- companion not opened
      | some h => if h.ok then rgContainsToken h rg tok else true

/-- Every bound column must pass. A row group is a candidate only when
    each bound-presence bit is set. -/
def rgPassesAll (rg : Nat)
    (ohS : Option BitmapHandle) (boundS : Option Nat)
    (ohP : Option BitmapHandle) (boundP : Option Nat)
    (ohO : Option BitmapHandle) (boundO : Option Nat) : Bool :=
  rgCouldContain ohS rg boundS && rgCouldContain ohP rg boundP &&
  rgCouldContain ohO rg boundO

def BitmapHandle.numRgs (h : BitmapHandle) : Nat := h.header.numRgs
def BitmapHandle.numTokens (h : BitmapHandle) : Nat := h.header.numTokens

/-! ## Soundness

`BuiltCorrectly h occurs` says the bitmap agrees with the ground truth
`occurs rg tok` — "token `tok` appears in some row of row group `rg`" —
at every in-range pair.

The lemma is the contrapositive the prune call site needs: given that
agreement, a `false` from `rgContainsToken` means the token really is
absent, so skipping the row group is sound.

⚠️ **What this does and does not establish.** The F\* module is explicit
that the same lemma is proved *in the form stated* while the real
obligation is elsewhere: nothing here shows `BuiltCorrectly` HOLDS of any
particular `.presence` file. That is the writer-side proof — a ghost
projection from the on-disk bytes to the token set of each row group,
plus a lemma that the builder respects it — and neither tree has it. The
statement is what callers rely on; the producer-side obligation is open
in both. -/

def OccursPred := Nat → Nat → Bool

def BuiltCorrectly (h : BitmapHandle) (occurs : OccursPred) : Prop :=
  ∀ rg tok, rg < h.header.numRgs → tok < h.header.numTokens →
    rgContainsToken h rg tok = occurs rg tok

theorem rgContainsToken_sound (h : BitmapHandle) (occurs : OccursPred)
    (rg tok : Nat) (hbuilt : BuiltCorrectly h occurs)
    (hrg : rg < h.header.numRgs) (htok : tok < h.header.numTokens)
    (hfalse : rgContainsToken h rg tok = false) :
    occurs rg tok = false := by
  rw [← hbuilt rg tok hrg htok]; exact hfalse

/-! ## Build-time checks

A bitmap is built here from its bytes, so the format is stated by
construction rather than described. -/

/-- `numRgs` row groups by `numTokens` tokens, with `set` listing the
    `(rg, tok)` pairs whose bit is on. -/
def mkPresence (numRgs numTokens : Nat) (set : List (Nat × Nat)) : ByteArray :=
  let bits := numRgs * numTokens
  let nbytes := (bits + 7) / 8
  let hdr : List UInt8 :=
    [0x43, 0x4F, 0x54, 0x50,            -- 'C','O','T','P' little-endian u32
     0x01, 0x00, 0x00, 0x00,            -- version 1
     UInt8.ofNat (numRgs % 256), UInt8.ofNat (numRgs / 256), 0, 0,
     UInt8.ofNat (numTokens % 256), UInt8.ofNat (numTokens / 256), 0, 0]
  let body := (List.range nbytes).map (fun byteIdx =>
    (List.range 8).foldl (fun acc b =>
      let bitIndex := byteIdx * 8 + b
      let rg := bitIndex / numTokens
      let tok := bitIndex % numTokens
      if bitIndex < bits && set.contains (rg, tok) then acc + UInt8.ofNat (2 ^ b)
      else acc) 0)
  ⟨(hdr ++ body).toArray⟩

private def bm : ByteArray := mkPresence 3 5 [(0, 0), (0, 4), (1, 2), (2, 3)]

#guard (readPresenceHeader bm).isSome
#guard (readPresenceHeader bm).map (·.magic) == some cotpMagicU32
#guard (readPresenceHeader bm).map (·.numRgs) == some 3
#guard (readPresenceHeader bm).map (·.numTokens) == some 5
#guard (openBitmapBytes bm).isSome

private def hb : BitmapHandle := (openBitmapBytes bm).getD ⟨ByteArray.empty, default⟩

/-! Every set bit reads back, and no unset bit does. Checked over the
    WHOLE grid, so a bit-order or row-major error cannot hide in a
    corner. -/

#guard (List.range 3).all (fun rg => (List.range 5).all (fun tok =>
  rgContainsToken hb rg tok == [(0,0),(0,4),(1,2),(2,3)].contains (rg, tok)))

/-! ### The safe-direction defaults

An out-of-range INDEX answers `false` — no row group, nothing skipped
wrongly. An out-of-range READ answers `true` — a short file says nothing
about the data. These are different situations and they fall opposite
ways; a port that made them agree would be wrong in one of them. -/

#guard !rgContainsToken hb 3 0          -- rg past numRgs
#guard !rgContainsToken hb 0 5          -- tok past numTokens
#guard !rgContainsToken hb 99 99

private def truncated : BitmapHandle :=
  { hb with bytes := hb.bytes.extract 0 presenceHeaderSize }   -- header only

#guard rgContainsToken truncated 0 1     -- would be false in a full file
#guard !rgContainsToken hb 0 1

/-! ### The wrapper's fallbacks -/

#guard rgCouldContain (some hb) 0 none          -- unbound column
#guard rgCouldContain none 0 (some 1)           -- companion absent
#guard rgCouldContain (some hb) 0 (some 0)      -- bit set
#guard !rgCouldContain (some hb) 0 (some 1)     -- bit clear

/-! A handle whose header is invalid over-includes rather than being
    trusted. `openBitmapBytes` refuses such a file, so this is the
    belt-and-braces path the F\* keeps. -/

private def badHeader : BitmapHandle :=
  { hb with header := { hb.header with magic := cotdMagicU32 } }

#guard !badHeader.ok
#guard rgCouldContain (some badHeader) 0 (some 1)

/-! A `.dict` companion must not open as a `.presence` one — the two
    magics differ by one byte. -/

#guard cotpMagicU32 != cotdMagicU32
#guard (openBitmapBytes ⟨(([0x43, 0x4F, 0x54, 0x44] : List UInt8) ++
          List.replicate 12 (0 : UInt8)).toArray⟩).isNone

/-! ### The AND form

A row group passes only when EVERY bound column's bit is set. -/

#guard rgPassesAll 0 (some hb) (some 0) (some hb) (some 4) (some hb) none
#guard !rgPassesAll 0 (some hb) (some 0) (some hb) (some 1) (some hb) none
#guard rgPassesAll 0 none none none none none none

#print axioms rgContainsToken_sound

end L4Factoidal.Cottas
