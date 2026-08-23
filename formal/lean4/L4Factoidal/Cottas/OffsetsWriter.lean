/-
L4Factoidal.Cottas.OffsetsWriter — the `.p.offsets` serialiser.

Port of `formal/fstar/RDF.CottasStore.OffsetsWriter.fst` (404 lines).
The companion file that maps a `(row group, predicate)` bucket to the
sorted subject ids it holds.

## The format

```
Header (16 bytes, little-endian throughout):
  [ magic     : u32  'COTO' = 0x4F544F43 ]
  [ version   : u32  currently 1 ]
  [ numRgs    : u32 ]
  [ numPreds  : u32 ]

Index:
  [ rgOffsets : u64[numRgs * numPreds + 1]
                byte offset where bucket `rg * numPreds + pred` starts;
                the trailing entry is the end-of-file sentinel. ]

Payload:
  [ subjectIds : u32[]  sorted ascending within each bucket ]
```

## Three changes from the F\* module

**It writes the whole file.** F\* writes the 16-byte header and leaves
the index and the payload to the OCaml glue
(`experimental_ocaml_glue/cottas_ondisk_zzzzzz_lamed3_offset_idx.sh`),
for the cons-cell reason `PresenceWriter` gives. `ByteArray` has no such
cost.

**Byte offsets, not counts.** `parse_offsets` in the F\* module reads
the last index entry as a COUNT OF SUBJECT IDS. The OCaml writer sets
`cur = data_offset0 = 16 + 8 * (num_rgs * num_preds + 1)` and advances
by `4 * bucket_length`, and its own comment says "byte offset where
row-list starts". So the F\* parser asks for far more u32 values than
remain and returns `None` on every `.p.offsets` file the project
writes. This is the same fault as
<https://github.com/danbri/factoidal/issues/555> in
`CompoundPresenceWriter`, which is where it was first found; that issue
asks for this module to be checked, and this is the answer — it is
present here too.

**An out-of-range entry fails the write instead of truncating it.**
`serialize_u32_list` in F\* returns `[]` at the first entry at or above
2^32, which drops every remaining byte of the payload while the header
still declares the full count. The file is then short and unreadable,
and nothing said so at write time. `buildOffsets` returns `none` for
the whole file instead.

## What is proved, and what is not

`bucketsSorted` states the reader-side precondition — each bucket
strictly ascending, hence duplicate-free — and
`buildOffsets_bucketsSorted` proves `buildOffsets` establishes it, via
the shared `sortByKey_sorted`. The writer-reader agreement itself is
checked by `#guard` at several shapes and is NOT proved; see the same
note in `PresenceWriter`.
-/
import L4Factoidal.Cottas.CompoundPresenceWriter

namespace L4Factoidal.Cottas

def cotoMagicU32 : UInt32 := 0x4F544F43
def offsetsLayoutVersion : UInt32 := 1
def offsetsHeaderSize : Nat := 16

structure OffsetsHeader where
  magic    : UInt32
  version  : UInt32
  numRgs   : Nat
  numPreds : Nat
  deriving Repr, DecidableEq, Inhabited

def OffsetsHeader.ok (h : OffsetsHeader) : Bool :=
  h.magic == cotoMagicU32 && h.version == offsetsLayoutVersion

def buildOffsetsHeader (numRgs numPreds : UInt32) : List UInt8 :=
  writeU32Le cotoMagicU32 ++ writeU32Le offsetsLayoutVersion ++
  writeU32Le numRgs ++ writeU32Le numPreds

/-- The 16-byte header alone — the one function the OCaml glue calls. -/
def serializeOffsetsHeader (numRgs numPreds : Nat) : Option (List UInt8) :=
  if numRgs ≥ 4294967296 || numPreds ≥ 4294967296 then none
  else some (buildOffsetsHeader (UInt32.ofNat numRgs) (UInt32.ofNat numPreds))

/-! ## The buckets

`buckets[rg * numPreds + pred]` is the subject-id list of that bucket.
`buildOffsets` sorts each one and drops repeats. -/

def sortSubjects : List Nat → List Nat := sortByKey id

def bucketsSorted (buckets : List (List Nat)) : Bool :=
  buckets.all (sortedByKey id)

def offsetsDataStart (numRgs numPreds : Nat) : Nat :=
  offsetsHeaderSize + 8 * (numRgs * numPreds + 1)

/-- `none` when a header count overflows u32, when the bucket count is
    not `numRgs * numPreds`, or when a subject id does not fit in u32. -/
def buildOffsets (numRgs numPreds : Nat) (buckets : List (List Nat)) :
    Option ByteArray :=
  if buckets.length != numRgs * numPreds then none
  else if buckets.any (fun b => b.any (fun s => s ≥ 4294967296)) then none
  else
    let sorted := buckets.map sortSubjects
    (serializeOffsetsHeader numRgs numPreds).map (fun hdr =>
      let index := (prefixOffsets (offsetsDataStart numRgs numPreds)
                      (sorted.map (fun b => 4 * b.length))).flatMap writeU64Le
      let body := sorted.flatMap (fun b =>
                    b.flatMap (fun s => writeU32Le (UInt32.ofNat s)))
      ⟨(hdr ++ index ++ body).toArray⟩)

theorem buildOffsets_bucketsSorted (buckets : List (List Nat)) :
    bucketsSorted (buckets.map sortSubjects) = true := by
  simp only [bucketsSorted, List.all_eq_true, List.mem_map]
  rintro b ⟨c, _, rfl⟩
  exact sortByKey_sorted id c

/-! ## Reading it back -/

structure OffsetsHandle where
  bytes  : ByteArray
  header : OffsetsHeader

def readOffsetsHeader (bs : ByteArray) : Option OffsetsHeader := do
  let magic ← readU32Le bs 0
  let version ← readU32Le bs 4
  let numRgs ← readU32Le bs 8
  let numPreds ← readU32Le bs 12
  some { magic := magic, version := version,
         numRgs := numRgs.toNat, numPreds := numPreds.toNat }

def openOffsetsBytes (bs : ByteArray) : Option OffsetsHandle :=
  match readOffsetsHeader bs with
  | none   => none
  | some h => if h.ok then some { bytes := bs, header := h } else none

def openOffsets (path : System.FilePath) : IO (Option OffsetsHandle) := do
  if !(← path.pathExists) then return none
  return openOffsetsBytes (← IO.FS.readBinFile path)

def readIndexEntry (h : OffsetsHandle) (i : Nat) : Option Nat :=
  if i > h.header.numRgs * h.header.numPreds then none
  else readU64Le h.bytes (offsetsHeaderSize + 8 * i)

/-- The subject ids of bucket `(rg, pred)`. `none` when the bucket is
    out of range, the index is unreadable, the span is negative or not
    a whole number of u32 entries, or the payload is truncated. -/
def bucketSubjects (h : OffsetsHandle) (rg pred : Nat) : Option (List Nat) :=
  if rg ≥ h.header.numRgs || pred ≥ h.header.numPreds then none
  else
    let i := rg * h.header.numPreds + pred
    match readIndexEntry h i, readIndexEntry h (i + 1) with
    | some startOff, some endOff =>
        if endOff < startOff || (endOff - startOff) % 4 != 0 then none
        else (List.range ((endOff - startOff) / 4)).mapM
               (fun k => (readU32Le h.bytes (startOff + 4 * k)).map UInt32.toNat)
    | _, _ => none

/-- Inverse of `buildOffsets`, recovering the bucket structure. -/
def parseOffsets (bs : ByteArray) : Option (Nat × Nat × List (List Nat)) := do
  let h ← openOffsetsBytes bs
  let buckets ← (List.range (h.header.numRgs * h.header.numPreds)).mapM
                  (fun i => bucketSubjects h (i / h.header.numPreds)
                              (i % h.header.numPreds))
  some (h.header.numRgs, h.header.numPreds, buckets)

/-! ## Build-time checks

### The round trip -/

private def ort (numRgs numPreds : Nat) (buckets : List (List Nat)) : Bool :=
  match buildOffsets numRgs numPreds buckets with
  | none    => false
  | some bs =>
      match parseOffsets bs with
      | none => false
      | some (r, p, back) =>
          r == numRgs && p == numPreds && back == buckets.map sortSubjects

#guard ort 0 0 []
#guard ort 1 1 [[7]]
#guard ort 2 3 [[1, 2], [], [9], [4, 4, 4], [], [0, 100, 50]]
#guard ort 3 1 [[], [], []]
#guard ort 1 4 [[5], [6], [7], [8]]

/-! ### Every bucket comes back at its own coordinates

A round trip that recovered the right MULTISET of buckets in the wrong
order would satisfy `ort` if the buckets happened to be symmetric.
These read individual `(rg, pred)` pairs. -/

private def obytes : ByteArray :=
  (buildOffsets 2 3 [[1, 2], [], [9], [4], [], [0, 100, 50]]).getD ByteArray.empty

private def oh : OffsetsHandle :=
  (openOffsetsBytes obytes).getD ⟨ByteArray.empty, default⟩

#guard bucketSubjects oh 0 0 == some [1, 2]
#guard bucketSubjects oh 0 1 == some []
#guard bucketSubjects oh 0 2 == some [9]
#guard bucketSubjects oh 1 0 == some [4]
#guard bucketSubjects oh 1 1 == some []
#guard bucketSubjects oh 1 2 == some [0, 50, 100]

/-! ### Out-of-range coordinates are refused -/

#guard (bucketSubjects oh 2 0).isNone
#guard (bucketSubjects oh 0 3).isNone

/-! ### A wrong magic or version is refused, and so is a `.presence`
    file or a `.po.presence` one -/

#guard (openOffsetsBytes ⟨(writeU32Le 0x44544F43 ++ writeU32Le 1 ++
          writeU32Le 0 ++ writeU32Le 0).toArray⟩).isNone
#guard (openOffsetsBytes ⟨(writeU32Le cotoMagicU32 ++ writeU32Le 2 ++
          writeU32Le 0 ++ writeU32Le 0).toArray⟩).isNone
#guard (openOffsetsBytes (mkPresence 2 2 [])).isNone
#guard (openOffsetsBytes (mkCompound 2 2 [[(1, 1)]])).isNone
#guard cotoMagicU32 != copoMagicU32
#guard cotoMagicU32 != cotpMagicU32

/-! ### A truncated file yields `none` for the affected bucket, not a
    short list read out of whatever bytes remain -/

#guard (bucketSubjects { oh with bytes := oh.bytes.extract 0 (oh.bytes.size - 4) }
          1 2).isNone

/-! ### The writer refuses, rather than truncating

The F\* `serialize_u32_list` returns `[]` at the first entry at or above
2^32, dropping the rest of the payload while the header still declares
the full count. -/

#guard (buildOffsets 1 1 [[4294967296]]).isNone
#guard (buildOffsets 1 1 [[1], [2]]).isNone          -- wrong bucket count
#guard (buildOffsets 4294967296 1 []).isNone

/-! ### Sorting and de-duplication happen on the writer's side -/

#guard sortSubjects [5, 1, 5, 3] == [1, 3, 5]
#guard bucketsSorted ([[5, 1, 5, 3], [2, 2]].map sortSubjects)
#guard !bucketsSorted [[5, 1]]

/-! ### The header the OCaml glue calls, byte for byte -/

#guard serializeOffsetsHeader 7 9 ==
  some (writeU32Le 0x4F544F43 ++ writeU32Le 1 ++ writeU32Le 7 ++ writeU32Le 9)
#guard (serializeOffsetsHeader 7 9).map List.length == some 16

/-! ### The F\* rule applied to a real file asks for more than it holds

`parse_offsets` takes the last index entry as a count of u32 subject
ids. Here that entry is the file size in bytes. -/

private def fstarConventionSubjectCount (bs : ByteArray) : Option Nat := do
  let h ← readOffsetsHeader bs
  let offs ← (List.range (h.numRgs * h.numPreds + 1)).mapM
               (fun i => readU64Le bs (offsetsHeaderSize + 8 * i))
  offs.getLast?

#guard (match fstarConventionSubjectCount obytes with
        | some k => k == obytes.size && k * 4 > obytes.size
        | none   => false)

#print axioms buildOffsets_bucketsSorted

end L4Factoidal.Cottas
