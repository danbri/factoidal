/-
L4Factoidal.Cottas.CompoundPresenceBitmap — the joint (p, o) companion.

Port of `formal/fstar/RDF.CottasStore.CompoundPresenceBitmap.fst` (362
lines). The reader for `<cottas>.po.presence`.

Where `PresenceBitmap` answers "does row group `rg` hold token `t` in
this column", this answers the JOINT question: "could row group `rg`
hold at least one row whose predicate token is `p` AND whose object
token is `o`?" When both are bound it is strictly more selective than
the per-column AND — a row group can hold `p` somewhere and `o`
somewhere without holding them in the same row.

## The file format

```
Header (20 bytes, little-endian throughout):
  [ magic         : u32  'COPO' = 0x4F504F43 ]
  [ version       : u32  currently 1 ]
  [ numRgs        : u32 ]
  [ predDictSize  : u32  cross-check against .p.dict ]
  [ objDictSize   : u32  cross-check against .o.dict ]

Index:
  [ rgOffsets : u64[numRgs + 1]
                byte offset where each row group's pair list begins;
                the trailing entry is the end-of-file sentinel. ]

Pair data (per row group, sorted):
  [ pairs : u64[]  bytes 0..3 = objId, bytes 4..7 = predId ]
```

The byte order is the point: the whole little-endian u64 is
`(predId << 32) ||| objId`, so ascending u64 order IS lexicographic
`(predId, objId)` order, and a binary search over the packed region
works directly.

`pairCode` builds that value with multiplication rather than a shift,
following the F\* source — there it is for purity, here it keeps the two
trees' arithmetic identical.

## The I/O, again at the edge

Same as `PresenceBitmap`: the F\* module reads through
`OnDiskIndex.fst`'s `assume val` primitives; this one is a pure function
of a `ByteArray` read once by `openCompound`.

## Safe-direction defaults

A prune's correctness is one-sided, and every default is carried over:

| Situation | Answer |
|---|---|
| `rg`, `p` or `o` out of range | `false` — no such row group or token |
| offsets unreadable, or end before start | `true` |
| binary search runs out of fuel | `true` |
| a pair read fails | `true` |
| row group's pair list is EMPTY | `false` — decisive |
| search completes without a hit | `false` — decisive |
| either term unbound | `true` — the compound gate says nothing |
| companion absent or header invalid | `true` |

The two decisive `false`s are what make the gate worth having; every
other row is an over-include.
-/
import L4Factoidal.Cottas.PresenceBitmap

namespace L4Factoidal.Cottas

def copoMagicU32 : UInt32 := 0x4F504F43
def compoundLayoutVersion : UInt32 := 1
def compoundHeaderSize : Nat := 20

structure CompoundHeader where
  magic        : UInt32
  version      : UInt32
  numRgs       : Nat
  predDictSize : Nat
  objDictSize  : Nat
  deriving Repr, DecidableEq, Inhabited

def CompoundHeader.ok (h : CompoundHeader) : Bool :=
  h.magic == copoMagicU32 && h.version == compoundLayoutVersion

def readU64Le (bs : ByteArray) (off : Nat) : Option Nat :=
  if off + 8 > bs.size then none
  else some ((List.range 8).foldr (fun i acc => acc * 256 + bs[off + i]!.toNat) 0)

def readCompoundHeader (bs : ByteArray) : Option CompoundHeader := do
  let magic ← readU32Le bs 0
  let version ← readU32Le bs 4
  let numRgs ← readU32Le bs 8
  let predDictSize ← readU32Le bs 12
  let objDictSize ← readU32Le bs 16
  some { magic := magic, version := version, numRgs := numRgs.toNat,
         predDictSize := predDictSize.toNat, objDictSize := objDictSize.toNat }

structure CompoundHandle where
  bytes  : ByteArray
  header : CompoundHeader

def CompoundHandle.ok (h : CompoundHandle) : Bool := h.header.ok

def openCompoundBytes (bs : ByteArray) : Option CompoundHandle :=
  match readCompoundHeader bs with
  | none   => none
  | some h => if h.ok then some { bytes := bs, header := h } else none

def openCompound (path : System.FilePath) : IO (Option CompoundHandle) := do
  if !(← path.pathExists) then return none
  return openCompoundBytes (← IO.FS.readBinFile path)

/-! ## Offsets and pair codes -/

def readRgStartOffset (h : CompoundHandle) (rg : Nat) : Option Nat :=
  if rg ≥ h.header.numRgs then none
  else readU64Le h.bytes (compoundHeaderSize + 8 * rg)

def readRgEndOffset (h : CompoundHandle) (rg : Nat) : Option Nat :=
  if rg ≥ h.header.numRgs then none
  else readU64Le h.bytes (compoundHeaderSize + 8 * (rg + 1))

/-- `(predId << 32) ||| objId`, written with multiplication as the F\*
    source does. -/
def pairCode (p o : Nat) : Nat := p * 4294967296 + o

/-! ## The search

The writer guarantees each row group's list is sorted ascending by u64
value, equivalently lexicographic `(predId, objId)`. Inclusive-bounds
binary search; the fuel is the totality witness. -/

def compoundBsearch (bs : ByteArray) (startOff npairs target lo hi : Nat) :
    Nat → Bool
  | 0     => true                         -- out of fuel: over-include
  | f + 1 =>
      if lo > hi then false               -- decisive negative
      else
        let mid := lo + (hi - lo) / 2
        if mid ≥ npairs then true         -- out of bounds: over-include
        else
          match readU64Le bs (startOff + 8 * mid) with
          | none      => true             -- read failed: over-include
          | some code =>
              if code == target then true
              else if code > target then
                if mid == 0 then false
                else compoundBsearch bs startOff npairs target lo (mid - 1) f
              else compoundBsearch bs startOff npairs target (mid + 1) hi f

def rgCouldContainPair (h : CompoundHandle) (rg p o : Nat) : Bool :=
  if rg ≥ h.header.numRgs then false
  else if p ≥ h.header.predDictSize then false
  else if o ≥ h.header.objDictSize then false
  else
    match readRgStartOffset h rg, readRgEndOffset h rg with
    | some startOff, some endOff =>
        if endOff < startOff then true
        else
          let npairs := (endOff - startOff) / 8
          if npairs == 0 then false       -- empty row group: decisive
          else compoundBsearch h.bytes startOff npairs (pairCode p o)
                 0 (npairs - 1) (npairs + 1)
    | _, _ => true

/-- The compound gate says nothing unless BOTH terms are bound. -/
def rgPassesPair (h : CompoundHandle) (rg : Nat)
    (boundP boundO : Option Nat) : Bool :=
  match boundP, boundO with
  | some p, some o => rgCouldContainPair h rg p o
  | _, _ => true

def compoundRgPassesPair (oh : Option CompoundHandle) (rg : Nat)
    (boundP boundO : Option Nat) : Bool :=
  match oh with
  | none   => true
  | some h => if h.ok then rgPassesPair h rg boundP boundO else true

/-- Both gates: the per-column one and the joint one. A `false` from
    either is sound to skip. -/
def rgPassesCompoundAndPerColumn (rg : Nat)
    (ohCompound : Option CompoundHandle)
    (ohS : Option BitmapHandle) (boundS : Option Nat)
    (ohP : Option BitmapHandle) (boundP : Option Nat)
    (ohO : Option BitmapHandle) (boundO : Option Nat) : Bool :=
  rgPassesAll rg ohS boundS ohP boundP ohO boundO &&
  compoundRgPassesPair ohCompound rg boundP boundO

def CompoundHandle.numRgs (h : CompoundHandle) : Nat := h.header.numRgs
def CompoundHandle.predDictSize (h : CompoundHandle) : Nat := h.header.predDictSize
def CompoundHandle.objDictSize (h : CompoundHandle) : Nat := h.header.objDictSize

/-! ## Soundness

Same shape and the same open obligation as `PresenceBitmap`: the lemma
holds given that the file agrees with the ground truth, and nothing here
shows any actual `.po.presence` file does. The writer is in OCaml and
the producer-side proof is open in both trees. -/

def PairOccursPred := Nat → Nat → Nat → Bool

def CompoundBuiltCorrectly (h : CompoundHandle) (pairOccurs : PairOccursPred) : Prop :=
  ∀ rg p o, rg < h.header.numRgs → p < h.header.predDictSize →
    o < h.header.objDictSize → rgCouldContainPair h rg p o = pairOccurs rg p o

theorem rgCouldContainPair_sound (h : CompoundHandle) (pairOccurs : PairOccursPred)
    (rg p o : Nat) (hbuilt : CompoundBuiltCorrectly h pairOccurs)
    (hrg : rg < h.header.numRgs) (hp : p < h.header.predDictSize)
    (ho : o < h.header.objDictSize)
    (hfalse : rgCouldContainPair h rg p o = false) :
    pairOccurs rg p o = false := by
  rw [← hbuilt rg p o hrg hp ho]; exact hfalse

/-! ## Build-time checks

The file is built here, so the format is stated by construction. -/

private def u32le (n : Nat) : List UInt8 :=
  [UInt8.ofNat (n % 256), UInt8.ofNat ((n / 256) % 256),
   UInt8.ofNat ((n / 65536) % 256), UInt8.ofNat ((n / 16777216) % 256)]

private def u64le (n : Nat) : List UInt8 :=
  u32le (n % 4294967296) ++ u32le (n / 4294967296)

/-- `rgs` gives, per row group, its SORTED list of `(p, o)` pairs. -/
def mkCompound (predDictSize objDictSize : Nat) (rgs : List (List (Nat × Nat))) :
    ByteArray :=
  let numRgs := rgs.length
  let indexBytes := 8 * (numRgs + 1)
  let dataStart := compoundHeaderSize + indexBytes
  let offsets := rgs.foldl (fun acc rg => acc ++ [acc.getLast! + 8 * rg.length])
                   [dataStart]
  let hdr := u32le 0x4F504F43 ++ u32le 1 ++ u32le numRgs
             ++ u32le predDictSize ++ u32le objDictSize
  let index := offsets.flatMap u64le
  let body := rgs.flatMap (fun rg => rg.flatMap (fun (p, o) => u64le (pairCode p o)))
  ⟨(hdr ++ index ++ body).toArray⟩

private def cbytes : ByteArray :=
  mkCompound 10 10 [[(1, 2), (1, 5), (3, 4)], [], [(2, 2)]]

#guard (readCompoundHeader cbytes).map (·.magic) == some copoMagicU32
#guard (readCompoundHeader cbytes).map (·.numRgs) == some 3
#guard (readCompoundHeader cbytes).map (·.predDictSize) == some 10
#guard (openCompoundBytes cbytes).isSome

private def ch : CompoundHandle := (openCompoundBytes cbytes).getD ⟨ByteArray.empty, default⟩

/-! Every stored pair is found, and pairs that are not stored are NOT —
    including `(1, 4)` and `(3, 2)`, which are the CROSS products of
    stored pairs. Those two are the reason the compound bitmap exists:
    row group 0 holds predicate 1 and predicate 3, and objects 2, 4 and
    5, so a per-column AND would admit both. The joint gate rejects
    them. -/

#guard rgCouldContainPair ch 0 1 2
#guard rgCouldContainPair ch 0 1 5
#guard rgCouldContainPair ch 0 3 4
#guard !rgCouldContainPair ch 0 1 4
#guard !rgCouldContainPair ch 0 3 2
#guard rgCouldContainPair ch 2 2 2
#guard !rgCouldContainPair ch 2 1 2

/-! An EMPTY row group is a decisive `false`, not an over-include. Row
    group 1 has no pairs. -/

#guard !rgCouldContainPair ch 1 1 2
#guard !rgCouldContainPair ch 1 2 2

/-! Out-of-range indices are `false` — no such row group or token. -/

#guard !rgCouldContainPair ch 3 1 2
#guard !rgCouldContainPair ch 0 10 2
#guard !rgCouldContainPair ch 0 1 10

/-! A truncated file over-includes: the offsets do not read, so the
    answer falls the safe way. Contrast with the decisive `false`s
    above — a port that collapsed these two would be wrong. -/

private def ctrunc : CompoundHandle :=
  { ch with bytes := ch.bytes.extract 0 compoundHeaderSize }

#guard rgCouldContainPair ctrunc 0 1 4      -- would be false in a full file
#guard !rgCouldContainPair ch 0 1 4

/-! The pair code packs predicate high, object low, so ascending u64
    order is lexicographic `(p, o)` — which is what makes the binary
    search valid. -/

#guard pairCode 1 2 < pairCode 1 5
#guard pairCode 1 5 < pairCode 3 4
#guard pairCode 0 4294967295 < pairCode 1 0

/-! The gate is silent unless BOTH terms are bound. -/

#guard rgPassesPair ch 0 (some 1) none
#guard rgPassesPair ch 0 none (some 4)
#guard rgPassesPair ch 0 none none
#guard !rgPassesPair ch 0 (some 1) (some 4)

#guard compoundRgPassesPair none 0 (some 1) (some 4)
#guard compoundRgPassesPair (some ch) 0 (some 1) (some 2)
#guard !compoundRgPassesPair (some ch) 0 (some 1) (some 4)

/-! A `.presence` file must not open as a `.po.presence` one. -/

#guard copoMagicU32 != cotpMagicU32
#guard (openCompoundBytes (mkPresence 2 2 [])).isNone

#print axioms rgCouldContainPair_sound

end L4Factoidal.Cottas
