/-
L4Factoidal.Cottas.CompoundPresenceWriter — the `.po.presence` serialiser.

Port of `formal/fstar/RDF.CottasStore.CompoundPresenceWriter.fst` (394
lines): the writer whose reader is
`L4Factoidal.Cottas.CompoundPresenceBitmap`.

## What the F\* module does, and the two changes here

The F\* module writes the 20-byte header and leaves the two large
arrays — the row-group offset index and the packed pair codes — to the
OCaml glue
(`experimental_ocaml_glue/cottas_ondisk_zzzzzzzzzzzzz_compound_po_writer.sh`),
for the cons-cell reason `PresenceWriter` gives. `ByteArray` has no such
cost, so this module writes the whole file.

The second change is the offset convention, and it is a correction
rather than a widening. See the section at the end of this file: the
F\* module's own round-trip parser reads the offset index in units the
shipping writer does not use, so it returns `none` on every real
`.po.presence` file. This module uses the convention the reader and the
OCaml writer both use — byte offsets from the start of the file.

## The sorted-unique invariant becomes the writer's job

The reader binary-searches each row group's pair list, so the list must
be sorted ascending by `pairCode`. In the F\* module that is a caller
obligation, stated in a comment as "NOT enforced here". Here
`buildCompoundPresence` sorts and de-duplicates, and
`sortPairs_sorted` proves the result satisfies the predicate. That
closes the reader's precondition on the writer's side by proof rather
than by comment.
-/
import L4Factoidal.Cottas.CompoundPresenceBitmap
import L4Factoidal.Cottas.PresenceWriter
import L4Factoidal.Cottas.SortByKey

namespace L4Factoidal.Cottas

/-! ## Header -/

def writeU64Le (n : Nat) : List UInt8 :=
  (List.range 8).map (fun i => UInt8.ofNat ((n / (256 ^ i)) % 256))

def buildCompoundHeader (numRgs predDictSize objDictSize : UInt32) : List UInt8 :=
  writeU32Le copoMagicU32 ++ writeU32Le compoundLayoutVersion ++
  writeU32Le numRgs ++ writeU32Le predDictSize ++ writeU32Le objDictSize

/-- The 20-byte header alone — the one function the OCaml glue calls.
    `none` when a count overflows u32; the reader checks the same
    bound. -/
def serializeCompoundPresenceHeader (numRgs predDictSize objDictSize : Nat) :
    Option (List UInt8) :=
  if numRgs ≥ 4294967296 || predDictSize ≥ 4294967296 || objDictSize ≥ 4294967296
  then none
  else some (buildCompoundHeader (UInt32.ofNat numRgs) (UInt32.ofNat predDictSize)
               (UInt32.ofNat objDictSize))

/-! ## Sorting the pairs

`pairCode p o = p * 2^32 + o`, so ascending code order is lexicographic
`(predicate, object)` order — the order the reader's binary search
assumes. -/

def pairCodeOf (x : Nat × Nat) : Nat := pairCode x.1 x.2

/-- Strictly ascending by `pairCode`, hence duplicate-free — the order
    `rgCouldContainPair`'s binary search assumes. -/
def sortedByCode : List (Nat × Nat) → Bool := sortedByKey pairCodeOf

def sortPairs : List (Nat × Nat) → List (Nat × Nat) := sortByKey pairCodeOf

/-! ### The reader's precondition, proved of the writer's output

The sort and its proof live in `Cottas/SortByKey.lean`, shared with
`OffsetsWriter`, which needs the same property for its subject-id
buckets. -/

theorem sortPairs_sorted (l : List (Nat × Nat)) : sortedByCode (sortPairs l) = true :=
  sortByKey_sorted pairCodeOf l

/-! ## The offset index -/

/-- Running byte offsets: `start`, then `start` plus each successive
    row group's byte length. One entry per row group, plus the
    end-of-file sentinel. -/
def prefixOffsets (start : Nat) : List Nat → List Nat
  | []      => [start]
  | n :: ns => start :: prefixOffsets (start + n) ns

def compoundDataStart (numRgs : Nat) : Nat := compoundHeaderSize + 8 * (numRgs + 1)

def compoundRgOffsets (rgs : List (List (Nat × Nat))) : List Nat :=
  prefixOffsets (compoundDataStart rgs.length) (rgs.map (fun rg => 8 * rg.length))

/-! ## The whole file -/

/-- A complete `.po.presence` file. Each row group's pairs are sorted
    and de-duplicated here, so the reader's binary-search precondition
    holds by `sortPairs_sorted`.

    `none` when a header count overflows u32. Pair components are not
    bounded here: `pairCode` is total, and a component at or above 2^32
    would corrupt the packing, so the caller's dictionary sizes are the
    place that bound is enforced — the reader rejects any token at or
    above the declared dictionary size. -/
def buildCompoundPresence (predDictSize objDictSize : Nat)
    (rgs : List (List (Nat × Nat))) : Option ByteArray :=
  let sorted := rgs.map sortPairs
  (serializeCompoundPresenceHeader sorted.length predDictSize objDictSize).map
    (fun hdr =>
      let index := (compoundRgOffsets sorted).flatMap writeU64Le
      let body := sorted.flatMap (fun rg => rg.flatMap (fun x => writeU64Le (pairCodeOf x)))
      ⟨(hdr ++ index ++ body).toArray⟩)

/-! ## Round trip -/

def decodePair (code : Nat) : Nat × Nat := (code / 4294967296, code % 4294967296)

/-- The pairs in `[startOff, endOff)`. `none` on a truncated file or a
    span that is not a whole number of 8-byte codes. -/
def readPairsRange (bs : ByteArray) (startOff endOff : Nat) :
    Option (List (Nat × Nat)) :=
  if endOff < startOff || (endOff - startOff) % 8 != 0 then none
  else (List.range ((endOff - startOff) / 8)).mapM
         (fun i => (readU64Le bs (startOff + 8 * i)).map decodePair)

/-- Inverse of `buildCompoundPresence`, recovering the PER-ROW-GROUP
    structure rather than one flat pair list. -/
def parseCompoundPresence (bs : ByteArray) :
    Option (Nat × Nat × List (List (Nat × Nat))) := do
  let h ← readCompoundHeader bs
  if !h.ok then none else do
  let offs ← (List.range (h.numRgs + 1)).mapM
               (fun i => readU64Le bs (compoundHeaderSize + 8 * i))
  let rgs ← (List.range h.numRgs).mapM
              (fun rg => readPairsRange bs offs[rg]! offs[rg + 1]!)
  some (h.predDictSize, h.objDictSize, rgs)

/-! ## Build-time checks

### The round trip -/

private def crt (predSize objSize : Nat) (rgs : List (List (Nat × Nat))) : Bool :=
  match buildCompoundPresence predSize objSize rgs with
  | none    => false
  | some bs =>
      match parseCompoundPresence bs with
      | none => false
      | some (p, o, back) =>
          p == predSize && o == objSize && back == rgs.map sortPairs

#guard crt 0 0 []
#guard crt 10 10 [[(1, 2), (1, 5), (3, 4)], [], [(2, 2)]]
#guard crt 10 10 [[], [], []]
#guard crt 4 4 [[(3, 3), (0, 0), (1, 1), (2, 2)]]

/-! ### The sort is a sort: it orders, de-duplicates and keeps the set -/

#guard sortPairs [(3, 4), (1, 5), (1, 2)] == [(1, 2), (1, 5), (3, 4)]
#guard sortPairs [(1, 2), (1, 2), (1, 2)] == [(1, 2)]
#guard sortedByCode (sortPairs [(9, 1), (0, 7), (9, 0), (0, 7)])
#guard (sortPairs [(9, 1), (0, 7), (9, 0)]).length == 3

/-! ### The writer and the reader agree, position by position

The whole `predDictSize × objDictSize` grid for every row group,
compared against the ground-truth pair set. This is what
`CompoundBuiltCorrectly` assumes and neither tree proves; it is
computational evidence at these shapes, not a proof for all shapes.
The `PresenceWriter` note applies here word for word: a theorem taking
the agreement as a hypothesis and concluding the agreement would prove
nothing, and is not written. -/

private def compoundReaderAgrees (predSize objSize : Nat)
    (rgs : List (List (Nat × Nat))) : Bool :=
  match buildCompoundPresence predSize objSize rgs with
  | none    => false
  | some bs =>
      match openCompoundBytes bs with
      | none   => false
      | some h =>
          (List.range rgs.length).all (fun rg =>
            (List.range predSize).all (fun p =>
              (List.range objSize).all (fun o =>
                rgCouldContainPair h rg p o == (rgs[rg]!.contains (p, o)))))

#guard compoundReaderAgrees 10 10 [[(1, 2), (1, 5), (3, 4)], [], [(2, 2)]]
#guard compoundReaderAgrees 4 4 [[(0, 0), (1, 1), (2, 2), (3, 3)], [(3, 0)]]
#guard compoundReaderAgrees 3 3 [[]]
#guard compoundReaderAgrees 5 5 [[(0, 0)], [(4, 4)], [(2, 1), (2, 3)]]

/-! And the agreement is not vacuous: these fixtures answer `true`
    somewhere and `false` somewhere, including at the CROSS products a
    per-column gate would admit. -/

#guard (buildCompoundPresence 10 10 [[(1, 2), (3, 4)]]).isSome
#guard (match buildCompoundPresence 10 10 [[(1, 2), (3, 4)]] with
        | some bs => match openCompoundBytes bs with
                     | some h => rgCouldContainPair h 0 1 2 && !rgCouldContainPair h 0 1 4
                     | none   => false
        | none    => false)

/-! ### The header the OCaml glue calls, byte for byte -/

#guard serializeCompoundPresenceHeader 3 10 20 ==
  some (writeU32Le 0x4F504F43 ++ writeU32Le 1 ++ writeU32Le 3 ++
        writeU32Le 10 ++ writeU32Le 20)
#guard (serializeCompoundPresenceHeader 4294967296 0 0).isNone
#guard (serializeCompoundPresenceHeader 0 4294967296 0).isNone
#guard (serializeCompoundPresenceHeader 0 0 4294967296).isNone
#guard (serializeCompoundPresenceHeader 3 10 20).map List.length == some 20

/-! ### Agreement with the reader module's own fixture builder

`CompoundPresenceBitmap.mkCompound` builds a test file directly. Two
independent constructions of the same format, compared. -/

#guard (buildCompoundPresence 10 10 [[(1, 2), (1, 5), (3, 4)], [], [(2, 2)]]).map (·.toList)
       == some (mkCompound 10 10 [[(1, 2), (1, 5), (3, 4)], [], [(2, 2)]]).toList

/-! ## ⚠️ The F\* module's round-trip parser reads a different format

`RDF.CottasStore.CompoundPresenceWriter.fst` carries
`parse_compound_presence` and a round-trip lemma
`lemma_parse_serialize_compound_presence`. Its hypothesis includes

```
last_of_or rg_offsets 0 == FStar.List.Tot.length pairs
```

so it reads the final offset entry as a COUNT OF PAIRS. The shipping
writer and the reader both use BYTE OFFSETS from the start of the
file: the OCaml glue sets `cur = data_offset0 = 20 + 8 * (num_rgs + 1)`
before the loop, and `CompoundPresenceBitmap` computes
`npairs = (endOff - startOff) / 8` and reads a code at
`startOff + 8 * mid`.

Under the real convention the final entry is
`20 + 8 * (numRgs + 1) + 8 * totalPairs`, which exceeds `totalPairs`
for every input. `parse_compound_presence` then asks for that many u64
values, more bytes than the file holds, and returns `None`. So the F\*
parser returns `None` on every `.po.presence` file the project writes,
and the round-trip lemma — true as stated, about a matched
serialise/parse pair — covers no real file.

Only `serialize_compound_presence_header` is on the shipping path; the
glue calls it and writes the index and data itself. The mismatch is
therefore latent rather than a live fault, which is why it survived.

Filed as <https://github.com/danbri/factoidal/issues/555>. This module
uses the byte-offset convention, so its writer and its reader are the
same format, and `crt` above round-trips through it. -/

/-! The claim above is checked, not asserted: the F\* rule applied to a
    real file asks for more u64 entries than the file can hold. -/

private def fstarConventionPairCount (bs : ByteArray) : Option Nat := do
  let h ← readCompoundHeader bs
  let offs ← (List.range (h.numRgs + 1)).mapM
               (fun i => readU64Le bs (compoundHeaderSize + 8 * i))
  offs.getLast?

#guard (match buildCompoundPresence 10 10 [[(1, 2), (1, 5), (3, 4)], [], [(2, 2)]] with
        | some bs =>
            match fstarConventionPairCount bs with
            | some k => k == 20 + 8 * 4 + 8 * 4 && k * 8 > bs.size
            | none   => false
        | none => false)

#print axioms sortPairs_sorted

end L4Factoidal.Cottas
