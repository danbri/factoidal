/-
L4Factoidal.Cottas.BaseWriterDict — layer 4 of the port of
`RDF.CottasStore.BaseWriter`: dictionary encoding, and the choice
between it and DLBA.

The predicate and graph columns of a COTTAS file repeat heavily, so
RLE_DICTIONARY is much smaller for them. The F\* source keeps BOTH
encoders and picks per column by measuring, which is the only way to be
right for a column whose cardinality is not known in advance.

## The pipeline

    values → sort → dedup → index → per-row lookup → maximal runs

`mergeSortStrings` and `dedupSortedStr` build the dictionary,
`dictTreeOfSorted` turns it into a balanced lookup tree so each row
costs a logarithmic walk rather than a linear scan, and `groupRuns`
collapses the resulting index stream into maximal runs for the RLE
encoder.

## Where a dictionary encoder goes wrong

* **Dedup only works on a SORTED list.** `dedupSortedStr` compares
  adjacent elements and nothing else, so calling it on unsorted input
  silently keeps duplicates — and a dictionary with duplicates makes
  two indices for one value, which a reader cannot detect.
  `dedup_unsorted_keeps_duplicates` exhibits that, so the ordering
  requirement is a checked fact rather than a comment.
* **`groupRuns` collapses ADJACENT equal indices only.** That is what
  RLE means, and it is also why the sort above matters for size but not
  for correctness. `groupRuns_nonAdjacent_stays_split` pins it.
* **The run header is `(run_length << 1) | 0`**, a PLAIN varint — the
  same non-zigzag rule as a binary field's length, and the third place
  in this writer where the two varint kinds sit next to each other.

## Choosing by measuring

`encodeColumnChooseSmaller` builds both and keeps the shorter. The F\*
source does the same. A column of all-distinct values is where the
dictionary loses, and `#guard` covers both directions so the comparison
cannot silently become a constant.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.Cottas.BaseWriterColumn

namespace L4Factoidal.Cottas.BaseWriterDict

open L4Factoidal.Cottas.BaseWriterPrims
open L4Factoidal.Cottas.BaseWriterThrift
open L4Factoidal.Cottas.BaseWriterColumn

/-! ## 1. Ordering -/

def strLt (a b : String) : Bool := a < b
def strLe (a b : String) : Bool := a ≤ b

/-! ## 2. Sort, dedup, index -/

def mergeSortedStr : List String → List String → Nat → List String → List String
  | xs, ys, 0, acc => acc.reverse ++ xs ++ ys
  | [], [], _ + 1, acc => acc.reverse
  | [], hd :: tl, f + 1, acc => mergeSortedStr [] tl f (hd :: acc)
  | hd :: tl, [], f + 1, acc => mergeSortedStr tl [] f (hd :: acc)
  | hx :: tx, hy :: ty, f + 1, acc =>
      if strLe hx hy then mergeSortedStr tx (hy :: ty) f (hx :: acc)
      else mergeSortedStr (hx :: tx) ty f (hy :: acc)

def mergeSortStringsFuel (xs : List String) : Nat → List String
  | 0 => xs
  | depth + 1 =>
      match xs with
      | [] => []
      | [_] => xs
      | _ :: _ :: _ =>
          let n := xs.length
          let left := xs.take (n / 2)
          let right := xs.drop (n / 2)
          let sl := mergeSortStringsFuel left depth
          let sr := mergeSortStringsFuel right depth
          mergeSortedStr sl sr (sl.length + sr.length) []

def mergeSortStrings (xs : List String) : List String :=
  mergeSortStringsFuel xs (xs.length + 1)

/-- Drop adjacent duplicates. **Correct only on a sorted list** — see
the module header. -/
def dedupSortedStr : List String → List String
  | [] => []
  | [x] => [x]
  | x :: y :: tl => if x == y then dedupSortedStr (y :: tl) else x :: dedupSortedStr (y :: tl)

def zipWithIndex (xs : List String) : List (String × Nat) :=
  xs.zipIdx

/-! ## 3. The lookup tree

A balanced tree over the sorted dictionary, so a per-row lookup is a
logarithmic walk rather than a linear scan. -/

inductive DictTree where
  | leaf
  | node (l : DictTree) (k : String) (idx : Nat) (r : DictTree)

def dictTreeOfSorted (xs : List (String × Nat)) : Nat → DictTree
  | 0 => .leaf
  | n + 1 =>
      let mid := (n + 1) / 2
      match xs.drop mid with
      | [] => .leaf
      | (k, v) :: right =>
          .node (dictTreeOfSorted (xs.take mid) mid) k v
                (dictTreeOfSorted right (n - mid))

def dictTreeFind (v : String) : DictTree → Option Nat
  | .leaf => none
  | .node l k idx r =>
      if v == k then some idx
      else if strLt v k then dictTreeFind v l else dictTreeFind v r

def lookupIndices (values : List String) (t : DictTree) : List Nat :=
  -- a value absent from the tree cannot arise: the tree is built from
  -- the same values
  values.map (fun v => (dictTreeFind v t).getD 0)

/-! ## 4. Maximal runs -/

def groupRunsAcc : List Nat → Nat → Nat → List (Nat × Nat) → List (Nat × Nat)
  | [], curVal, curCount, acc => ((curVal, curCount) :: acc).reverse
  | v :: tl, curVal, curCount, acc =>
      if v == curVal then groupRunsAcc tl curVal (curCount + 1) acc
      else groupRunsAcc tl v 1 ((curVal, curCount) :: acc)

/-- Collapse ADJACENT equal indices. Non-adjacent equals stay separate
runs, which is what RLE means. -/
def groupRuns : List Nat → List (Nat × Nat)
  | [] => []
  | v :: tl => groupRunsAcc tl v 1 []

/-! ## 5. Dictionary and data pages -/

/-- One PLAIN dictionary entry: a little-endian 32-bit length, then the
bytes. NOT a varint length — that is the DLBA rule, and mixing the two
is the mistake this comment and the `#guard` below exist to prevent. -/
def writeDictEntry (s : String) : Bytes :=
  let b := s.toUTF8.toList
  writeU32Le b.length ++ b

def buildDictPagePayload (entries : List String) : Bytes :=
  entries.flatMap writeDictEntry

/-- The def-level section, then a one-byte index bit width, then the
RLE-only hybrid index stream. -/
def buildRleDictionaryPagePayload (valueCount bitWidth : Nat)
    (runs : List (Nat × Nat)) : Bytes :=
  defLevelSection valueCount ++ [UInt8.ofNat (bitWidth % 256)]
  ++ buildRleRuns ((bitWidth + 7) / 8) runs

/-! ## 6. Choosing by measuring -/

inductive ColumnEncoding where
  | dlba
  | rleDictionary
  deriving DecidableEq, Repr

structure ColEncoded where
  kind : ColumnEncoding
  numValues : Nat
  /-- Zero for `dlba`: there is no dictionary page at all. -/
  dictPageLen : Nat
  /-- The FULL byte length of this column's pages. -/
  totalLen : Nat
  deriving Repr

/-- The dictionary for a column: sorted, deduplicated. -/
def columnDictionary (values : List String) : List String :=
  dedupSortedStr (mergeSortStrings values)

/-- Both encodings, measured. -/
def encodeColumnSizes (values : List String) : ColEncoded × ColEncoded :=
  let dictEntries := columnDictionary values
  let tree := dictTreeOfSorted (zipWithIndex dictEntries) dictEntries.length
  let indices := lookupIndices values tree
  let runs := groupRuns indices
  let bitWidth := bitsNeeded (if dictEntries.isEmpty then 0 else dictEntries.length - 1)
  let dictPage := buildDictPagePayload dictEntries
  let dataPage := buildRleDictionaryPagePayload values.length bitWidth runs
  let dlbaBlock := dlbaLengthBlock values
  let dlbaPage := defLevelSection values.length ++ dlbaBlock.2 ++ concatStringsBytes values
  ({ kind := .dlba, numValues := values.length, dictPageLen := 0
   , totalLen := dlbaPage.length },
   { kind := .rleDictionary, numValues := values.length
   , dictPageLen := dictPage.length
   , totalLen := dictPage.length + dataPage.length })

/-- Build both and keep the shorter, as the F* source does. -/
def encodeColumnChooseSmaller (values : List String) : ColEncoded :=
  let (dlba, dict) := encodeColumnSizes values
  if dict.totalLen < dlba.totalLen then dict else dlba

/-! ## 7. Where a dictionary encoder goes wrong -/

/-- **Dedup only works on a SORTED list.** On unsorted input it keeps
duplicates, and a dictionary with duplicates gives two indices for one
value — which a reader cannot detect. -/
theorem dedup_unsorted_keeps_duplicates :
    dedupSortedStr ["a", "b", "a"] = ["a", "b", "a"] := by decide

/-! Sorting first fixes it. Stated as a build-time check rather than a
theorem: the kernel does not reduce `String` comparison, so `decide`
cannot close it and `native_decide` is banned in this tree. -/
#guard dedupSortedStr (mergeSortStrings ["a", "b", "a"]) == ["a", "b"]

/-- **`groupRuns` collapses ADJACENT equal indices only.** -/
theorem groupRuns_nonAdjacent_stays_split :
    groupRuns [1, 2, 1] = [(1, 1), (2, 1), (1, 1)] := by decide

theorem groupRuns_adjacent_collapses :
    groupRuns [1, 1, 1] = [(1, 3)] := by decide

theorem groupRuns_nil : groupRuns [] = [] := rfl

/-- The choice is between the two the sizer built, never a third
thing. -/
theorem encodeColumnChooseSmaller_is_one_of (values : List String) :
    encodeColumnChooseSmaller values = (encodeColumnSizes values).1
    ∨ encodeColumnChooseSmaller values = (encodeColumnSizes values).2 := by
  simp only [encodeColumnChooseSmaller]
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-! ## Build-time checks -/

/-! Sorting and dedup. -/
#guard mergeSortStrings ["c", "a", "b"] == ["a", "b", "c"]
#guard mergeSortStrings ([] : List String) == ([] : List String)
#guard mergeSortStrings ["a"] == ["a"]
#guard dedupSortedStr ["a", "a", "b", "b", "b"] == ["a", "b"]
#guard columnDictionary ["b", "a", "b"] == ["a", "b"]

/-! The lookup tree finds every value it was built from, and nothing
else. -/
#guard (dictTreeFind "b"
          (dictTreeOfSorted (zipWithIndex ["a", "b", "c"]) 3)) == some 1
#guard (dictTreeFind "a"
          (dictTreeOfSorted (zipWithIndex ["a", "b", "c"]) 3)) == some 0
#guard (dictTreeFind "z"
          (dictTreeOfSorted (zipWithIndex ["a", "b", "c"]) 3)) == (none : Option Nat)

/-! Per-row indices, then maximal runs. -/
#guard lookupIndices ["b", "b", "a"]
        (dictTreeOfSorted (zipWithIndex ["a", "b"]) 2) == [1, 1, 0]
#guard groupRuns [1, 1, 0] == [(1, 2), (0, 1)]
#guard groupRuns [1, 2, 1] == [(1, 1), (2, 1), (1, 1)]

/-! A dictionary entry is a little-endian 32-bit length, NOT a varint —
the opposite of DLBA's length block. -/
#guard writeDictEntry "ab" == [(2 : UInt8), 0, 0, 0, (97 : UInt8), (98 : UInt8)]
#guard buildDictPagePayload [] == ([] : Bytes)

/-! **The measurement goes both ways.** A repeating column is smaller
dictionary-encoded; an all-distinct column is not. -/
#guard (encodeColumnChooseSmaller ["aaaa", "aaaa", "aaaa", "aaaa"]).kind
        == ColumnEncoding.rleDictionary
#guard (encodeColumnChooseSmaller ["a", "b", "c", "d"]).kind == ColumnEncoding.dlba
#guard (encodeColumnChooseSmaller ["a", "b", "c", "d"]).dictPageLen == 0
#guard (encodeColumnChooseSmaller ["aaaa", "aaaa", "aaaa", "aaaa"]).dictPageLen > 0
#guard (encodeColumnChooseSmaller ["a", "b"]).numValues == 2

/-! ## Axiom audit -/

#print axioms dedup_unsorted_keeps_duplicates
#print axioms groupRuns_nonAdjacent_stays_split
#print axioms groupRuns_adjacent_collapses
#print axioms encodeColumnChooseSmaller_is_one_of

end L4Factoidal.Cottas.BaseWriterDict
