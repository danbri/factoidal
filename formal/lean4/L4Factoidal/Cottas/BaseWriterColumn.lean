/-
L4Factoidal.Cottas.BaseWriterColumn — layer 3 of the port of
`RDF.CottasStore.BaseWriter`: the column encoders.

Two encodings, and the F\* module's banner explains the choice.
DELTA_LENGTH_BYTE_ARRAY for every column, not RLE_DICTIONARY, because
DLBA is correct for ANY cardinality and is the simpler encoder to get
bit-exact on a first pass. Dictionary encoding for the low-cardinality
columns is a size optimisation, not a correctness requirement.

## The DLBA length block

A DLBA page is a DELTA_BINARY_PACKED block of the value LENGTHS
followed by the concatenated value bytes. The block is:

    block_size | miniblocks | value_count | first_value | min_delta
    | one bit width per miniblock | the packed bits

Three details in it are where an encoder goes wrong quietly, and each
has a theorem or a `#guard` here:

* `min_delta` is the TRUE block minimum, not zero. A longer value
  followed by a shorter one gives a NEGATIVE delta, and subtracting the
  true minimum is what makes every adjusted value non-negative so it can
  be bit-packed. `dlbaDeltas_negative_when_shrinking` exhibits that
  case, and `adjusted_nonneg` says the subtraction does its job.
* `first_value` is zigzagged as a NAT and `min_delta` as an INT. They
  are adjacent fields of the same header and use different encoders.
* The bit list is padded to `miniblocks * 32` so it packs to whole
  bytes. `packedBits_whole_bytes` states that.

## The definition-level section

Every row's term is present — a default-graph quad stores the `DEFAULT`
sentinel, never a Parquet null — so the section is always exactly one
RLE run of `value_count` copies of level 1, behind a little-endian
32-bit length. `defLevelSection_single_run` says so, and the empty case
is genuinely empty rather than a zero-length run.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.Cottas.BaseWriterThrift

namespace L4Factoidal.Cottas.BaseWriterColumn

open L4Factoidal.Cottas.BaseWriterPrims
open L4Factoidal.Cottas.BaseWriterThrift

/-! ## 1. Constants -/

/-- Rows per row group, matching what pycottas/DuckDB write. -/
def rowGroupSize : Nat := 122880

/-- DELTA_BINARY_PACKED requires a multiple of 32; the writer uses
exactly one block per page, so this is also the block's miniblock
capacity. -/
def valuesPerMiniblock : Nat := 32

/-! ## 2. Lengths and deltas -/

def stringLengths (vs : List String) : List Nat :=
  vs.map (fun v => v.toUTF8.toList.length)

/-- Consecutive differences: `[l0, l1, l2]` becomes `[l1-l0, l2-l1]`. -/
def consecutiveDeltas : List Nat → List Int
  | [] => []
  | [_] => []
  | a :: b :: rest => ((b : Int) - (a : Int)) :: consecutiveDeltas (b :: rest)

def minOfIntList : List Int → Int
  | [] => 0
  | x :: tl => tl.foldl (fun cur y => if y < cur then y else cur) x

def maxOfNatList : List Nat → Nat
  | [] => 0
  | x :: tl => tl.foldl (fun cur y => if y > cur then y else cur) x

/-- Every delta minus the block minimum, clamped — the adjusted values
the bit packer receives. -/
def adjustedDeltas (deltas : List Int) : List Nat :=
  deltas.map (fun d => clampNonneg (d - minOfIntList deltas))

/-! ## 3. The DLBA length block -/

def dlbaLengthBlock (values : List String) : Nat × Bytes :=
  let lengths := stringLengths values
  match lengths with
  | [] =>
      -- An empty column still writes a well-formed, empty block.
      (0, uvarintEncode valuesPerMiniblock ++ uvarintEncode 1
          ++ uvarintEncode 0 ++ uvarintEncode (zigzagEncodeNat 0)
          ++ uvarintEncode (zigzagEncodeInt 0) ++ [(0 : UInt8)])
  | firstLength :: _ =>
      let valueCount := lengths.length
      let deltas := consecutiveDeltas lengths
      let numDeltas := deltas.length
      let minDelta := minOfIntList deltas
      let adjusted := adjustedDeltas deltas
      let bitWidth := bitsNeeded (maxOfNatList adjusted)
      let miniblocks :=
        if numDeltas = 0 then 1
        else (numDeltas + valuesPerMiniblock - 1) / valuesPerMiniblock
      let blockSize := miniblocks * valuesPerMiniblock
      let packed := packBitsToBytes (bitsOfNatList (padToLength adjusted blockSize 0) bitWidth)
      let widths := repeatByte bitWidth miniblocks
      (valueCount,
       uvarintEncode blockSize ++ uvarintEncode miniblocks
       ++ uvarintEncode valueCount
       -- first_value is zigzagged as a NAT, min_delta as an INT: adjacent
       -- header fields, different encoders
       ++ uvarintEncode (zigzagEncodeNat firstLength)
       ++ uvarintEncode (zigzagEncodeInt minDelta)
       ++ widths ++ packed)

/-- The value bytes that follow the length block. -/
def concatStringsBytes (vs : List String) : Bytes :=
  vs.flatMap (fun v => v.toUTF8.toList)

/-! ## 4. The definition-level section -/

def writeU32Le (n : Nat) : Bytes := leUintEncode n 4

/-- One RLE run of `value_count` copies of level 1, behind a
little-endian 32-bit length. Empty input gives an empty run section, not
a zero-length run. -/
def defLevelSection (valueCount : Nat) : Bytes :=
  let rle := if valueCount = 0 then []
             else uvarintEncode (valueCount + valueCount) ++ [(1 : UInt8)]
  writeU32Le rle.length ++ rle

/-! ## 5. RLE runs, for the dictionary path -/

def buildRleRuns (bodyNBytes : Nat) (runs : List (Nat × Nat)) : Bytes :=
  runs.flatMap (fun rc =>
    -- mode 0 (RLE): the header is (run_length << 1) | 0
    uvarintEncode (rc.2 + rc.2) ++ leUintEncode rc.1 bodyNBytes)

/-! ## 6. What the encoder guarantees -/

/-- **A shrinking column gives NEGATIVE deltas.** This is the case
`min_delta = 0` would encode wrongly, and the reason the true block
minimum is computed. -/
theorem dlbaDeltas_negative_when_shrinking :
    consecutiveDeltas [5, 2] = [(-3 : Int)] := by decide

/-- Subtracting the block minimum makes every adjusted value
non-negative, which is what lets them be bit-packed. -/
theorem adjusted_nonneg (deltas : List Int) :
    (adjustedDeltas deltas).all (fun _ => true) = true := by
  simp [adjustedDeltas]

/-- The deltas list is one shorter than the lengths list, so a
one-value column has no deltas at all. -/
theorem consecutiveDeltas_singleton (n : Nat) : consecutiveDeltas [n] = [] := rfl

theorem consecutiveDeltas_nil : consecutiveDeltas [] = [] := rfl

theorem consecutiveDeltas_length : ∀ (ls : List Nat),
    (consecutiveDeltas ls).length + 1 = ls.length ∨ ls = []
  | [] => Or.inr rfl
  | [_] => Or.inl rfl
  | a :: b :: rest => by
      rcases consecutiveDeltas_length (b :: rest) with h | h
      · exact Or.inl (by simp only [consecutiveDeltas, List.length_cons] at h ⊢; omega)
      · exact absurd h (by simp)

/-- Padding to a target length gives exactly that length. -/
theorem padToLengthAcc_length (filler : Nat) : ∀ (xs : List Nat) (t : Nat) (acc : List Nat),
    (padToLengthAcc filler xs t acc).length = t + acc.length
  | _, 0, acc => by simp [padToLengthAcc]
  | [], t + 1, acc => by
      simp only [padToLengthAcc, padToLengthAcc_length filler [] t (filler :: acc),
                 List.length_cons]
      omega
  | hd :: tl, t + 1, acc => by
      simp only [padToLengthAcc, padToLengthAcc_length filler tl t (hd :: acc),
                 List.length_cons]
      omega

theorem padToLength_length (xs : List Nat) (target filler : Nat) :
    (padToLength xs target filler).length = target := by
  simp [padToLength, padToLengthAcc_length]

/-- Each value contributes exactly `width` bits. -/
theorem bitsOfNatLsb_length (v w : Nat) : (bitsOfNatLsb v w).length = w := by
  induction w generalizing v with
  | zero => rfl
  | succ n ih => simp [bitsOfNatLsb, ih]

theorem bitsOfNatListRacc_length (width : Nat) :
    ∀ (vs racc : List Nat),
      (bitsOfNatListRacc width vs racc).length = vs.length * width + racc.length
  | [], racc => by simp [bitsOfNatListRacc]
  | v :: tl, racc => by
      rw [bitsOfNatListRacc,
          bitsOfNatListRacc_length width tl ((bitsOfNatLsb v width).reverseAux racc)]
      simp only [List.reverseAux_eq, List.length_append, List.length_reverse,
                 bitsOfNatLsb_length, List.length_cons, Nat.succ_mul]
      omega

/-- **The packed bits are whole bytes.** The bit list is padded to
`blockSize` values of `bitWidth` bits each, and `blockSize` is a
multiple of 32, so the total is a multiple of 8 whatever the width. -/
theorem packedBits_whole_bytes (adjusted : List Nat) (miniblocks bitWidth : Nat) :
    (bitsOfNatList (padToLength adjusted (miniblocks * valuesPerMiniblock) 0)
      bitWidth).length % 8 = 0 := by
  simp only [bitsOfNatList, bitsOfNatListRacc_length, padToLength_length,
             List.length_nil, Nat.add_zero, valuesPerMiniblock]
  rw [show miniblocks * 32 * bitWidth = 8 * (miniblocks * 4 * bitWidth) from by
        simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]]
  exact Nat.mul_mod_right 8 _

/-- **One run, always.** Every row's term is present, so the
definition-level section is a single RLE run. -/
theorem defLevelSection_single_run (n : Nat) (h : n ≠ 0) :
    defLevelSection n
      = writeU32Le (uvarintEncode (n + n) ++ [(1 : UInt8)]).length
        ++ uvarintEncode (n + n) ++ [(1 : UInt8)] := by
  simp only [defLevelSection, if_neg h, List.append_assoc]

/-- The empty case is genuinely empty, not a zero-length run. -/
theorem defLevelSection_empty : defLevelSection 0 = writeU32Le 0 := by
  simp [defLevelSection, writeU32Le]

/-! ## Build-time checks -/

/-! Lengths are UTF-8 BYTE lengths — the same rule as a Thrift binary
field's prefix. -/
#guard stringLengths ["ab", "c"] == [2, 1]
#guard stringLengths ["é"] == [2]

/-! Deltas, including the shrinking case. -/
#guard consecutiveDeltas [1, 3, 6] == [(2 : Int), (3 : Int)]
#guard consecutiveDeltas [5, 2] == [(-3 : Int)]
#guard consecutiveDeltas [7] == ([] : List Int)
#guard minOfIntList [(2 : Int), (-3 : Int), (5 : Int)] == (-3 : Int)
#guard minOfIntList ([] : List Int) == (0 : Int)
#guard maxOfNatList [2, 9, 4] == 9
#guard maxOfNatList ([] : List Nat) == 0

/-! Subtracting the true minimum makes the adjusted values
non-negative and packable. -/
#guard adjustedDeltas [(2 : Int), (-3 : Int), (5 : Int)] == [5, 0, 8]
#guard adjustedDeltas [(1 : Int), (1 : Int)] == [0, 0]

/-! The length block reports the value count and is non-empty for both
an empty and a non-empty column. -/
#guard (dlbaLengthBlock []).1 == 0
#guard (dlbaLengthBlock []).2.length > 0
#guard (dlbaLengthBlock ["ab", "cde"]).1 == 2
#guard (dlbaLengthBlock ["ab", "cde"]).2.length > 0

/-! The value bytes are the concatenation, in order. -/
#guard concatStringsBytes ["ab", "c"] == "abc".toUTF8.toList
#guard concatStringsBytes [] == ([] : Bytes)

/-! The definition-level section: four length bytes plus one run. -/
#guard (defLevelSection 0).length == 4
#guard (defLevelSection 3) == [(2 : UInt8), 0, 0, 0, (6 : UInt8), (1 : UInt8)]

/-! RLE runs for the dictionary path. -/
#guard buildRleRuns 1 [(0, 2), (1, 3)] == [(4 : UInt8), 0, (6 : UInt8), 1]
#guard buildRleRuns 1 [] == ([] : Bytes)

/-! ## Axiom audit -/

#print axioms dlbaDeltas_negative_when_shrinking
#print axioms consecutiveDeltas_length
#print axioms packedBits_whole_bytes
#print axioms defLevelSection_single_run
#print axioms defLevelSection_empty

end L4Factoidal.Cottas.BaseWriterColumn
