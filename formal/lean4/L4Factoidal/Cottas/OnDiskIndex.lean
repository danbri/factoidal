/-
L4Factoidal.Cottas.OnDiskIndex — the COTTAS `.dict` reader and the
companion-set boot helpers.

Port of `formal/fstar/RDF.CottasStore.OnDiskIndex.fst` (425 lines).
Seven `assume val`s become none.

## What the F\* module holds, and where each half lives here

| Half | F\* | Lean |
|---|---|---|
| byte-range I/O primitives | seven `assume val`s over an mmap | `IO.FS.readBinFile` once, then pure `ByteArray` reads |
| `.presence` header + bit test | here, used by `PresenceBitmap.fst` | already in `Cottas/PresenceBitmap.lean` |
| `.dict` header, decode, binary search | here | here |
| companion-set boot | here | here |

The presence half is not duplicated: `PresenceBitmap.fst` opens this
module and calls its `presence_test_bit`, and the Lean port put that
function in `PresenceBitmap.lean`. This module imports it.

## The `.dict` layout

```
Header (32 bytes):
  [  0: magic        u32  'COTD' = 0x44544F43 ]
  [  4: version      u32 ]
  [  8: numTokens    u32 ]
  [ 12: padding      u32 ]
  [ 16: idsOffset    u64 ]
  [ 24: tokensOffset u64 ]

ids:          u32[numTokens]      at idsOffset
tokenBounds:  u64[numTokens + 1]  at tokensOffset, absolute byte
                                  positions of each token's bytes
token bytes:  packed
```

`ids` is sorted so that `token(ids[i])` ascends. The search reads
`ids[mid]`, decodes that token, and compares. So `ids` is a permutation
and NOT the identity in general — the `#guard`s below use a permuted
fixture, because a reader that ignored `ids` and searched by id would
pass an identity fixture.

## Two differences from the F\* reader

**A token slice that is not valid UTF-8 is refused.** F\*'s
`read_companion_string` is an `assume val` returning `option string`
over a byte range; nothing states what it does with invalid UTF-8.
`dictDecodeToken` here goes through `String.fromUTF8?`, so a corrupt
slice yields `none` rather than a string nobody can name.

**The three-way comparison is `compare`, not a hand-written walk.**
F\* hand-rolls `compare_string` with a codepoint loop, its own comment
saying F\* "doesn't expose a built-in 3-way string comparator on Tot".
Lean's `compare` on `String` is lexicographic on codepoints, which is
the same order. A `#guard` below pins that on a non-ASCII pair, because
the on-disk order is produced by a writer that compares BYTES, and byte
order and codepoint order agree for valid UTF-8 — which is why the
search works at all and is worth stating rather than assuming.
-/
import L4Factoidal.Cottas.PresenceBitmap

namespace L4Factoidal.Cottas

def dictHeaderSize : Nat := 32

structure DictHeader where
  magic        : UInt32
  version      : UInt32
  numTokens    : Nat
  idsOffset    : Nat
  tokensOffset : Nat
  deriving Repr, DecidableEq, Inhabited

def DictHeader.ok (h : DictHeader) : Bool :=
  h.magic == cotdMagicU32 && h.version == layoutVersion

def readDictU64Le (bs : ByteArray) (off : Nat) : Option Nat :=
  if off + 8 > bs.size then none
  else some ((List.range 8).foldr (fun i acc => acc * 256 + bs[off + i]!.toNat) 0)

def readDictHeader (bs : ByteArray) : Option DictHeader := do
  let magic ← readU32Le bs 0
  let version ← readU32Le bs 4
  let numTokens ← readU32Le bs 8
  let idsOffset ← readDictU64Le bs 16
  let tokensOffset ← readDictU64Le bs 24
  some { magic := magic, version := version, numTokens := numTokens.toNat,
         idsOffset := idsOffset, tokensOffset := tokensOffset }

/-- `id` to its raw column token. `none` for an out-of-range id, an
    unreadable bound, an end before its start, or a slice that is not
    valid UTF-8. -/
def dictDecodeToken (bs : ByteArray) (h : DictHeader) (id : Nat) :
    Option String :=
  if id ≥ h.numTokens then none
  else do
    let tokenStart ← readDictU64Le bs (h.tokensOffset + 8 * id)
    let tokenEnd ← readDictU64Le bs (h.tokensOffset + 8 * (id + 1))
    if tokenEnd < tokenStart || tokenEnd > bs.size then none
    else String.fromUTF8? (bs.extract tokenStart tokenEnd)

def readIdAt (bs : ByteArray) (h : DictHeader) (i : Nat) : Option Nat :=
  if i ≥ h.numTokens then none
  else (readU32Le bs (h.idsOffset + 4 * i)).map UInt32.toNat

/-- Inclusive-bounds binary search over `ids`. The fuel is the
    totality witness, as in the F\* original. -/
def bsearchLoop (bs : ByteArray) (h : DictHeader) (query : String) :
    Nat → Nat → Nat → Option Nat
  | _,  _,  0     => none
  | lo, hi, f + 1 =>
      if lo > hi then none
      else
        let mid := lo + (hi - lo) / 2
        match readIdAt bs h mid with
        | none => none
        | some idAtMid =>
            match dictDecodeToken bs h idAtMid with
            | none => none
            | some tok =>
                match compare query tok with
                | .eq => some idAtMid
                | .lt => if mid == 0 then none
                         else bsearchLoop bs h query lo (mid - 1) f
                | .gt => bsearchLoop bs h query (mid + 1) hi f

def dictEncodeToken (bs : ByteArray) (h : DictHeader) (query : String) :
    Option Nat :=
  if h.numTokens == 0 then none
  else bsearchLoop bs h query 0 (h.numTokens - 1) (h.numTokens + 1)

/-! ## The presence bit index stays inside the declared extent

The F\* lemma `presence_bit_index_bounded`. It is the invariant the
`.presence` writer relies on when it sizes its buffer to
`(numRgs * numTokens + 7) / 8` bytes: every bit index this reader can
compute for an in-bounds `(rg, tok)` fits inside that extent. -/

theorem presenceBitIndexBounded (numRgs numTokens rg tok : Nat)
    (hrg : rg < numRgs) (htok : tok < numTokens) :
    rg * numTokens + tok < numRgs * numTokens := by
  have h2 : (rg + 1) * numTokens ≤ numRgs * numTokens :=
    Nat.mul_le_mul_right numTokens hrg
  rw [Nat.succ_mul] at h2
  omega

/-! ## Companion-set boot

The F\* version keys everything by path and reaches the bytes through
the mmap primitives on every lookup. Here the two files are read once
and the status carries their bytes, so every lookup below is a pure
function. -/

structure CompanionStatus where
  dictBytes      : ByteArray
  presenceBytes  : ByteArray
  dictHeader     : Option DictHeader
  presenceHeader : Option PresenceHeader

/-- Both headers must parse, both must declare the expected layout, and
    their token counts must agree — they describe the same column. -/
def companionStatusOk (cs : CompanionStatus) : Bool :=
  match cs.dictHeader, cs.presenceHeader with
  | some dh, some ph => dh.ok && ph.ok && dh.numTokens == ph.numTokens
  | _, _ => false

def loadCompanionStatusBytes (dictBytes presenceBytes : ByteArray) :
    CompanionStatus :=
  { dictBytes := dictBytes, presenceBytes := presenceBytes,
    dictHeader := readDictHeader dictBytes,
    presenceHeader := readPresenceHeader presenceBytes }

def loadCompanionStatus (dictPath presencePath : System.FilePath) :
    IO CompanionStatus := do
  let d ← if ← dictPath.pathExists then IO.FS.readBinFile dictPath
          else pure ByteArray.empty
  let p ← if ← presencePath.pathExists then IO.FS.readBinFile presencePath
          else pure ByteArray.empty
  return loadCompanionStatusBytes d p

def companionEncode (cs : CompanionStatus) (tok : String) : Option Nat :=
  match cs.dictHeader with
  | none    => none
  | some dh => if !dh.ok then none else dictEncodeToken cs.dictBytes dh tok

def companionDecode (cs : CompanionStatus) (id : Nat) : Option String :=
  match cs.dictHeader with
  | none    => none
  | some dh => if !dh.ok then none else dictDecodeToken cs.dictBytes dh id

/-- `true` when the row group may hold the token. Absent or invalid
    presence information answers `true` — the over-include. -/
def companionRgCouldContain (cs : CompanionStatus) (rg tokId : Nat) : Bool :=
  match cs.presenceHeader with
  | none    => true
  | some ph => if !ph.ok then true else presenceTestBit cs.presenceBytes ph rg tokId

/-! ## Build-time checks

### A `.dict` file, built here

`tokens` are given in ID order. `ids` is the permutation that sorts
them, so it is NOT the identity and a search that ignored it fails. -/

private def u32leBytes (n : Nat) : List UInt8 :=
  [UInt8.ofNat (n % 256), UInt8.ofNat ((n / 256) % 256),
   UInt8.ofNat ((n / 65536) % 256), UInt8.ofNat ((n / 16777216) % 256)]

private def u64leBytes (n : Nat) : List UInt8 :=
  u32leBytes (n % 4294967296) ++ u32leBytes (n / 4294967296)

private def insertByStr (x : String × Nat) :
    List (String × Nat) → List (String × Nat)
  | []      => [x]
  | y :: ys => match compare x.1 y.1 with
               | .lt => x :: y :: ys
               | _   => y :: insertByStr x ys

private def sortByStr : List (String × Nat) → List (String × Nat)
  | []      => []
  | x :: xs => insertByStr x (sortByStr xs)

/-- `tokens` in id order; the file's `ids` array sorts them. -/
def mkDict (tokens : List String) : ByteArray :=
  let n := tokens.length
  let idsOffset := dictHeaderSize
  let tokensOffset := idsOffset + 4 * n
  let dataStart := tokensOffset + 8 * (n + 1)
  let tokenBytes := tokens.map (fun t => t.toUTF8.toList)
  let bounds := (tokenBytes.map List.length).foldl
                  (fun acc len => acc ++ [acc.getLast! + len]) [dataStart]
  let order := (sortByStr ((tokens.zipIdx).map (fun (t, i) => (t, i)))).map (·.2)
  let hdr := u32leBytes 0x44544F43 ++ u32leBytes 1 ++ u32leBytes n ++
             u32leBytes 0 ++ u64leBytes idsOffset ++ u64leBytes tokensOffset
  ⟨(hdr ++ order.flatMap u32leBytes ++ bounds.flatMap u64leBytes ++
    tokenBytes.flatten).toArray⟩

private def dtokens : List String :=
  ["zebra", "apple", "mango", "banana", "cherry"]

private def dbytes : ByteArray := mkDict dtokens
private def dh : DictHeader := (readDictHeader dbytes).getD default

#guard dh.ok
#guard dh.numTokens == 5
#guard dh.idsOffset == 32
#guard dh.tokensOffset == 32 + 4 * 5

/-! Decode: id `i` gives the i-th token of the INPUT list, so the ids
    are the input positions and the `ids` array is a separate
    permutation. -/

#guard dictDecodeToken dbytes dh 0 == some "zebra"
#guard dictDecodeToken dbytes dh 3 == some "banana"
#guard (dictDecodeToken dbytes dh 5).isNone

/-! The `ids` array is NOT the identity here — it sorts the tokens —
    so a search that read ids[mid] as mid would fail below. -/

#guard readIdAt dbytes dh 0 == some 1        -- "apple"
#guard readIdAt dbytes dh 4 == some 0        -- "zebra"
#guard (readIdAt dbytes dh 5).isNone

/-! Encode finds EVERY token at its own id, and rejects absent ones. -/

#guard (dtokens.zipIdx).all (fun (t, i) => dictEncodeToken dbytes dh t == some i)
#guard (dictEncodeToken dbytes dh "durian").isNone
#guard (dictEncodeToken dbytes dh "").isNone
#guard (dictEncodeToken dbytes dh "zebras").isNone
#guard (dictEncodeToken dbytes dh "apple ").isNone

/-! Encode and decode compose back to the identity on ids in range. -/

#guard (List.range 5).all (fun i =>
  match dictDecodeToken dbytes dh i with
  | some t => dictEncodeToken dbytes dh t == some i
  | none   => false)

/-! An empty dictionary: no id decodes and no token encodes. -/

#guard (readDictHeader (mkDict [])).map (·.numTokens) == some 0
#guard (dictEncodeToken (mkDict []) ((readDictHeader (mkDict [])).getD default)
          "anything").isNone

/-! ### Codepoint order and byte order agree on valid UTF-8

The writer that produces the on-disk `ids` array compares BYTES; this
reader compares codepoints. UTF-8 preserves codepoint order under
bytewise comparison, which is why the search works. Pinned on a
non-ASCII pair rather than assumed. -/

private def utok : List String := ["a", "z", "é", "ü", "中"]

#guard (utok.zipIdx).all (fun (t, i) =>
  dictEncodeToken (mkDict utok) ((readDictHeader (mkDict utok)).getD default) t
    == some i)

#guard compare "é" "ü" == compare "é".toUTF8.toList "ü".toUTF8.toList
#guard compare "z" "é" == compare "z".toUTF8.toList "é".toUTF8.toList

/-! ### Companion status

Both headers must parse, both must be valid, and their token counts
must agree. A dict of five tokens beside a presence bitmap declaring
four is refused — that pair describes two different columns. -/

private def okStatus : CompanionStatus :=
  loadCompanionStatusBytes dbytes (mkPresence 2 5 [(0, 1), (1, 3)])
private def mismatched : CompanionStatus :=
  loadCompanionStatusBytes dbytes (mkPresence 2 4 [])

#guard companionStatusOk okStatus
#guard !companionStatusOk mismatched
#guard !companionStatusOk (loadCompanionStatusBytes ByteArray.empty ByteArray.empty)

#guard companionEncode okStatus "mango" == some 2
#guard companionDecode okStatus 2 == some "mango"
#guard (companionEncode okStatus "durian").isNone

#guard companionRgCouldContain okStatus 0 1
#guard !companionRgCouldContain okStatus 0 3
#guard companionRgCouldContain okStatus 1 3

/-! Absent presence information is the over-include, never a skip. -/

#guard companionRgCouldContain
  (loadCompanionStatusBytes dbytes ByteArray.empty) 0 3

/-! A `.presence` file must not read as a `.dict` one. -/

#guard cotdMagicU32 != cotpMagicU32
#guard !((readDictHeader (mkPresence 2 2 [])).getD default).ok

#print axioms presenceBitIndexBounded

end L4Factoidal.Cottas
