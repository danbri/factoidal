/-
L4Factoidal.Storage.IndexedBlockWireV3Theorems — the round-trip proof for the
IBK3 block codec of `L4Factoidal.Storage.IndexedBlockWireV3`.

IBK3 writes a thirteen-byte header, then fixed-width sixteen-byte ID rows, then
a complete PTD1 paged term dictionary, then a CRC32C over every post-version
byte. `decode` reads all of that back, re-checks the framing, the row order and
the predicate locality, and rebuilds a block through `IndexedBlock.fromParts?`.
This module proves the two agree:

    encode? block = some bytes →
      ∃ decoded, decode bytes = some decoded ∧
        decoded.dict = block.dict ∧ decoded.rows = block.rows

`IndexedBlock.Block` also carries two hash maps, so block equality is not the
statement. The two array fields are what `IndexedBlock.Block.denotes` reads,
and `denotes_decode_encode?` draws the graph-level corollary from them.

The proof is layered. The byte-array bridge turns each `ByteArray` operation
the decoder performs into the list operation the encoder built. The positioned
row lemmas give `positionedRows` its three properties: it maps back to the
source rows, its length is the row count, and its positions are exactly the
indexes `canonicalOrder` checks. That last one is why `orderedRows?` takes its
direct path, so the proof never meets `Array.qsort`, about which Lean core has
no theorems. `decodeRowsGo_ok` lifts the four-field row read from one row to
the whole row area. `PagedTermDictionary.decode?_encode?` supplies the
dictionary round trip, and `ptd_pageTerms_of_encode?` supplies the page-size
check IBK3 re-runs on the PTD1 prefix.

Three conditions are hypotheses rather than consequences of `encode?`.
`hnodup` and `hwf` are the two `IndexedBlock.fromParts?` admission conditions
that `encode?` does not check, and `hfit` is the term-codec condition that no
`encode?` guard sees. The docstring of `decode_encode?` states each. No further
hypothesis was needed: every other check `decode` performs is discharged from
`encode?`'s own `supported` gate and its two size guards.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.IndexedBlockWireV3
import L4Factoidal.Storage.PagedTermDictionaryTheorems

namespace L4Factoidal.Storage.IndexedBlockWireV3

open L4Factoidal.RDF
open L4Factoidal.Storage
open L4Factoidal.Storage.IndexedBlock

/-! ## Byte array bridge -/

/-- The byte array built from a list has that list's length. -/
theorem size_byteArrayOfList (xs : List UInt8) :
    (byteArrayOfList xs).size = xs.length := by
  simp [byteArrayOfList, ByteArray.size]

/-- Reading a built byte array back gives the list it was built from. -/
theorem listOfByteArray_byteArrayOfList (xs : List UInt8) :
    listOfByteArray (byteArrayOfList xs) = xs := by
  simp [byteArrayOfList, listOfByteArray]

/-- Building from a byte array's own list returns that byte array. -/
theorem byteArrayOfList_listOfByteArray (bytes : ByteArray) :
    byteArrayOfList (listOfByteArray bytes) = bytes := by
  simp [byteArrayOfList, listOfByteArray]

/-- A byte-range extract is the corresponding list slice. -/
theorem extract_byteArrayOfList (xs : List UInt8) (a b : Nat) :
    (byteArrayOfList xs).extract a b = byteArrayOfList ((xs.drop a).take (b - a)) := by
  simp [byteArrayOfList, ByteArray.extract, ByteArray.copySlice]

/-- Indexed access agrees between the byte array and its list. -/
theorem getElem?_byteArrayOfList (xs : List UInt8) (i : Nat) :
    (byteArrayOfList xs)[i]? = xs[i]? := by
  by_cases h : i < xs.length
  · rw [getElem?_pos (byteArrayOfList xs) i (by simpa [byteArrayOfList, ByteArray.size] using h),
      getElem?_pos xs i h]
    rfl
  · rw [getElem?_neg (byteArrayOfList xs) i (by simpa [byteArrayOfList, ByteArray.size] using h),
      getElem?_neg xs i h]

/-- The row decoder's four-byte read is the little-endian list read. -/
theorem readU32At?_byteArrayOfList (xs : List UInt8) (off : Nat) :
    readU32At? (byteArrayOfList xs) off = readU32LE xs off := by
  simp only [readU32At?, readU32LE, getElem?_byteArrayOfList]
  have h0 : xs[off]? = (xs.drop off)[0]? := by simp [List.getElem?_drop]
  have h1 : xs[off + 1]? = (xs.drop off)[1]? := by simp [List.getElem?_drop]
  have h2 : xs[off + 2]? = (xs.drop off)[2]? := by simp [List.getElem?_drop]
  have h3 : xs[off + 3]? = (xs.drop off)[3]? := by simp [List.getElem?_drop]
  rw [h0, h1, h2, h3]
  generalize xs.drop off = d
  rcases d with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨e, t⟩⟩⟩⟩ <;> simp

/-! ## Positioned rows -/

/-- The pairing `positionedRows` applies to each source row and its index. -/
def positioned (pair : IdTriple × Nat) : PositionedIdTriple :=
  { position := pair.2, row := pair.1 }

/-- `positionedRows` is that pairing mapped over the indexed row list. -/
theorem positionedRows_eq (block : Block) :
    positionedRows block = block.rows.toList.zipIdx.map positioned := rfl

/-- Every encoded row occupies sixteen bytes. -/
theorem encodeRow_length (entry : PositionedIdTriple) : (encodeRow entry).length = 16 := by
  simp [encodeRow]

/-- A row list encodes to sixteen bytes per row. -/
theorem flatMap_encodeRow_length : ∀ (rows : List PositionedIdTriple),
    (rows.flatMap encodeRow).length = rows.length * 16 := by
  intro rows
  induction rows with
  | nil => simp
  | cons entry rest ih =>
      simp only [List.flatMap_cons, List.length_append, encodeRow_length, ih,
        List.length_cons]
      omega

/-- Positioning preserves the row list. -/
theorem map_row_map_positioned : ∀ (rows : List IdTriple) (start : Nat),
    ((rows.zipIdx start).map positioned).map PositionedIdTriple.row = rows := by
  intro rows
  induction rows with
  | nil => intro start; simp
  | cons row rest ih =>
      intro start
      simp only [List.zipIdx_cons, List.map_cons, positioned, ih (start + 1)]

/-- One positioned row per source row. -/
theorem length_map_positioned (rows : List IdTriple) (start : Nat) :
    ((rows.zipIdx start).map positioned).length = rows.length := by
  simp

/-- A positioned row carries a source row and an index inside the declared
    row extent. -/
theorem mem_map_positioned : ∀ (rows : List IdTriple) (start : Nat)
    (entry : PositionedIdTriple), entry ∈ (rows.zipIdx start).map positioned →
    entry.row ∈ rows ∧ entry.position < start + rows.length := by
  intro rows
  induction rows with
  | nil => intro start entry hmem; simp at hmem
  | cons row rest ih =>
      intro start entry hmem
      simp only [List.zipIdx_cons, List.map_cons, List.mem_cons] at hmem
      rcases hmem with hmem | hmem
      · subst hmem
        exact ⟨by simp [positioned], by simp [positioned]⟩
      · obtain ⟨hrow, hpos⟩ := ih (start + 1) entry hmem
        exact ⟨List.mem_cons_of_mem _ hrow, by simp only [List.length_cons]; omega⟩

/-- The encoder's positions are exactly the wire indexes the decoder checks. -/
theorem canonicalOrder_map_positioned : ∀ (rows : List IdTriple) (start : Nat),
    ((rows.zipIdx start).map positioned).zipIdx start |>.all
      (fun pair => pair.1.position == pair.2) := by
  intro rows
  induction rows with
  | nil => intro start; simp
  | cons row rest ih =>
      intro start
      simp only [List.zipIdx_cons, List.map_cons, List.all_cons, positioned,
        beq_self_eq_true, Bool.true_and]
      exact ih (start + 1)

/-! ## Fixed-width row decoding -/

/-- A four-byte row field is readable at the length of the framing before it. -/
theorem readU32At?_at (pre : List UInt8) (value : UInt32) (rest : List UInt8) :
    readU32At? (byteArrayOfList (pre ++ writeU32LE value ++ rest)) pre.length = some value := by
  rw [readU32At?_byteArrayOfList]
  exact readU32LE_append_writeU32LE pre value rest

/-- The row walk decodes every encoded row back, in wire order. The four bound
    conditions are the `fitsU32` guards of `IndexedBlockWireV1.supported`
    together with the source position being inside the row extent. -/
theorem decodeRowsGo_ok : ∀ (rows : List PositionedIdTriple) (pre : List UInt8)
    (reversed : List PositionedIdTriple),
    (∀ entry ∈ rows, entry.position < UInt32.size ∧ entry.row.s < UInt32.size ∧
      entry.row.p < UInt32.size ∧ entry.row.o < UInt32.size) →
    decodeRowsGo rows.length (byteArrayOfList (pre ++ rows.flatMap encodeRow))
        pre.length reversed = some (reversed.reverse ++ rows) := by
  intro rows
  induction rows with
  | nil => intro pre reversed _; simp [decodeRowsGo]
  | cons entry rest ih =>
      intro pre reversed hbound
      obtain ⟨hpos, hs, hp, ho⟩ := hbound entry (by simp)
      have h0 : readU32At? (byteArrayOfList (pre ++ (entry :: rest).flatMap encodeRow))
          pre.length = some (UInt32.ofNat entry.position) := by
        rw [show pre ++ (entry :: rest).flatMap encodeRow
            = pre ++ writeU32LE (UInt32.ofNat entry.position) ++
              (writeU32LE (UInt32.ofNat entry.row.s) ++
                writeU32LE (UInt32.ofNat entry.row.p) ++
                writeU32LE (UInt32.ofNat entry.row.o) ++ rest.flatMap encodeRow) by
          simp [encodeRow, List.append_assoc]]
        exact readU32At?_at _ _ _
      have h1 : readU32At? (byteArrayOfList (pre ++ (entry :: rest).flatMap encodeRow))
          (pre.length + 4) = some (UInt32.ofNat entry.row.s) := by
        rw [show pre ++ (entry :: rest).flatMap encodeRow
            = (pre ++ writeU32LE (UInt32.ofNat entry.position)) ++
              writeU32LE (UInt32.ofNat entry.row.s) ++
              (writeU32LE (UInt32.ofNat entry.row.p) ++
                writeU32LE (UInt32.ofNat entry.row.o) ++ rest.flatMap encodeRow) by
          simp [encodeRow, List.append_assoc],
          show pre.length + 4
            = (pre ++ writeU32LE (UInt32.ofNat entry.position)).length by simp]
        exact readU32At?_at _ _ _
      have h2 : readU32At? (byteArrayOfList (pre ++ (entry :: rest).flatMap encodeRow))
          (pre.length + 8) = some (UInt32.ofNat entry.row.p) := by
        rw [show pre ++ (entry :: rest).flatMap encodeRow
            = (pre ++ writeU32LE (UInt32.ofNat entry.position) ++
                writeU32LE (UInt32.ofNat entry.row.s)) ++
              writeU32LE (UInt32.ofNat entry.row.p) ++
              (writeU32LE (UInt32.ofNat entry.row.o) ++ rest.flatMap encodeRow) by
          simp [encodeRow, List.append_assoc],
          show pre.length + 8
            = (pre ++ writeU32LE (UInt32.ofNat entry.position) ++
                writeU32LE (UInt32.ofNat entry.row.s)).length by simp]
        exact readU32At?_at _ _ _
      have h3 : readU32At? (byteArrayOfList (pre ++ (entry :: rest).flatMap encodeRow))
          (pre.length + 12) = some (UInt32.ofNat entry.row.o) := by
        rw [show pre ++ (entry :: rest).flatMap encodeRow
            = (pre ++ writeU32LE (UInt32.ofNat entry.position) ++
                writeU32LE (UInt32.ofNat entry.row.s) ++
                writeU32LE (UInt32.ofNat entry.row.p)) ++
              writeU32LE (UInt32.ofNat entry.row.o) ++ rest.flatMap encodeRow by
          simp [encodeRow, List.append_assoc],
          show pre.length + 12
            = (pre ++ writeU32LE (UInt32.ofNat entry.position) ++
                writeU32LE (UInt32.ofNat entry.row.s) ++
                writeU32LE (UInt32.ofNat entry.row.p)).length by simp]
        exact readU32At?_at _ _ _
      have hnext : pre ++ (entry :: rest).flatMap encodeRow
          = (pre ++ encodeRow entry) ++ rest.flatMap encodeRow := by
        simp [List.append_assoc]
      have hoff : pre.length + rowBytes = (pre ++ encodeRow entry).length := by
        simp [rowBytes, encodeRow]
      have hentry :
          ({ position := (UInt32.ofNat entry.position).toNat,
             row := { s := (UInt32.ofNat entry.row.s).toNat,
                      p := (UInt32.ofNat entry.row.p).toNat,
                      o := (UInt32.ofNat entry.row.o).toNat } } : PositionedIdTriple)
            = entry := by
        rw [u32_toNat_ofNat_of_lt hpos, u32_toNat_ofNat_of_lt hs,
          u32_toNat_ofNat_of_lt hp, u32_toNat_ofNat_of_lt ho]
      rw [List.length_cons, decodeRowsGo]
      simp only [h0, h1, h2, h3, bind, Option.bind, hentry]
      rw [hnext, hoff, ih (pre ++ encodeRow entry) (entry :: reversed)
        (fun e he => hbound e (List.mem_cons_of_mem _ he))]
      simp

/-! ## Row order and predicate locality -/

/-- The encoder writes rows in canonical position order. -/
theorem canonicalOrder_positionedRows (block : Block) :
    canonicalOrder (positionedRows block) = true := by
  rw [canonicalOrder, positionedRows_eq]
  exact canonicalOrder_map_positioned block.rows.toList 0

/-- Canonical rows are admitted by the direct path and restore the row array. -/
theorem orderedRows?_positionedRows (block : Block) :
    orderedRows? block.rows.size (positionedRows block) = some block.rows := by
  have hlen : (positionedRows block).length = block.rows.size := by
    rw [positionedRows_eq]; simp
  rw [orderedRows?, if_neg (by simp [hlen]), if_pos (canonicalOrder_positionedRows block),
    positionedRows_eq, map_row_map_positioned]

/-- The decoder's predicate-locality check is the encoder's admission check. -/
theorem predicateLocal_rows (block : Block) :
    predicateLocal block.rows = onePredicate block := rfl

/-! ## Dictionary identity reconstruction -/

/-- A dictionary list without repeats builds an ID map, provided the running
    map holds none of its terms yet. -/
theorem buildIdMap_isSome : ∀ (terms : List Term) (next : TermId)
    (ids : Std.HashMap Term TermId), terms.Nodup → (∀ t ∈ terms, ids[t]? = none) →
    (buildIdMap terms next ids).isSome := by
  intro terms
  induction terms with
  | nil => intro next ids _ _; simp [buildIdMap]
  | cons term rest ih =>
      intro next ids hnodup hfresh
      have hterm : ids[term]? = none := hfresh term (by simp)
      have hnotmem : term ∉ rest := (List.nodup_cons.mp hnodup).1
      have hrest : rest.Nodup := (List.nodup_cons.mp hnodup).2
      rw [buildIdMap, if_neg (by simp [hterm])]
      refine ih (next + 1) (ids.insert term next) hrest ?_
      intro t ht
      rw [Std.HashMap.getElem?_insert, if_neg (by
        intro heq
        exact hnotmem ((beq_iff_eq.mp heq) ▸ ht))]
      exact hfresh t (List.mem_cons_of_mem _ ht)

/-- `fromParts?` returns the dictionary and rows it was given whenever the
    dictionary has no repeats and every row decodes to a triple position. -/
theorem fromParts?_ok (dict : Array Term) (rows : Array IdTriple)
    (hnodup : dict.toList.Nodup)
    (hwf : rows.toList.all (rowWellFormed dict) = true) :
    ∃ decoded, fromParts? dict rows = some decoded ∧
      decoded.dict = dict ∧ decoded.rows = rows := by
  have hids := buildIdMap_isSome dict.toList 0 ∅ hnodup
    (fun t _ => Std.HashMap.getElem?_empty)
  obtain ⟨ids, hids⟩ := Option.isSome_iff_exists.mp hids
  refine ⟨{ dict := dict, idByTerm := ids, rows := rows,
            byPredicate := rows.foldl addPartition ∅ }, ?_, rfl, rfl⟩
  rw [fromParts?]
  simp only [hids, bind, Option.bind, hwf, if_true]

/-! ## The paged dictionary prefix -/

/-- Anything PTD1 encodes declares the default page size in its prefix, which
    is what the IBK3 decoder re-checks before it reads the dictionary. -/
theorem ptd_pageTerms_of_encode? (terms : Array Term) (dictionary : ByteArray)
    (h : PagedTermDictionary.encode? terms = some dictionary) :
    ∃ header, PagedTermDictionary.decodePrefix
        (dictionary.extract 0 PagedTermDictionary.prefixBytes) = some header ∧
      header.pageTerms = PagedTermDictionary.defaultPageTerms := by
  simp only [PagedTermDictionary.encode?] at h
  split at h
  · exact absurd h (by simp)
  · rename_i hsupp
    split at h
    · exact absurd h (by simp)
    · rename_i hguard
      injection h with h
      subst h
      simp only [PagedTermDictionary.supported, PagedTermDictionary.fitsU32,
        Bool.not_eq_true', Bool.and_eq_false_iff] at hsupp hguard
      obtain ⟨-, hszfit⟩ := by simpa using hsupp
      obtain ⟨⟨hpcfit, -⟩, -⟩ := by simpa using hguard
      have hu32 : (4294967296 : Nat) = UInt32.size := rfl
      refine ⟨{ termCount := terms.size,
                pageTerms := PagedTermDictionary.defaultPageTerms,
                pageCount := (PagedTermDictionary.encodePages terms.toList).length },
              ?_, rfl⟩
      obtain ⟨P, hP⟩ : ∃ P, P = PagedTermDictionary.encodePages terms.toList := ⟨_, rfl⟩
      rw [← hP] at hpcfit ⊢
      obtain ⟨dir, hdir⟩ : ∃ dir, dir = (PagedTermDictionary.directoryFor P).flatMap
        PagedTermDictionary.encodeDirectory := ⟨_, rfl⟩
      rw [← hdir]
      obtain ⟨pay, hpay⟩ : ∃ pay, pay = writeU32LE (UInt32.ofNat terms.size) ++
        writeU32LE (UInt32.ofNat PagedTermDictionary.defaultPageTerms) ++
        writeU32LE (UInt32.ofNat P.length) ++ dir ++ P.flatten := ⟨_, rfl⟩
      rw [← hpay]
      obtain ⟨pre17, hpre17⟩ : ∃ q, q = writeU32LE PagedTermDictionary.magic ++
        [PagedTermDictionary.version] ++ writeU32LE (UInt32.ofNat terms.size) ++
        writeU32LE (UInt32.ofNat PagedTermDictionary.defaultPageTerms) ++
        writeU32LE (UInt32.ofNat P.length) := ⟨_, rfl⟩
      have hsplit : writeU32LE PagedTermDictionary.magic ++ [PagedTermDictionary.version] ++
          pay ++ writeU32LE (crc32c pay)
          = pre17 ++ (dir ++ P.flatten ++ writeU32LE (crc32c pay)) := by
        rw [hpay, hpre17]; simp [List.append_assoc]
      have htake : ((writeU32LE PagedTermDictionary.magic ++ [PagedTermDictionary.version] ++
          pay ++ writeU32LE (crc32c pay)).drop 0).take (PagedTermDictionary.prefixBytes - 0)
          = pre17 := by
        rw [List.drop_zero, hsplit]
        exact List.take_left' (by rw [hpre17]; simp [PagedTermDictionary.prefixBytes])
      rw [PagedTermDictionary.extract_byteArrayOfList, htake, hpre17]
      exact PagedTermDictionary.decodePrefix_ok terms.size PagedTermDictionary.defaultPageTerms
        P.length (hu32 ▸ hszfit) (by decide) (by decide) (hu32 ▸ hpcfit)
        (by rw [hP, PagedTermDictionary.encodePages_length]
            simp only [PagedTermDictionary.defaultPageTerms, Array.length_toList]
            omega)

/-! ## The fixed IBK3 header -/

/-- The thirteen-byte header decodes to the row count and dictionary byte
    length the encoder wrote. -/
theorem decodePrefix_ok (rowCount dictionaryBytes : Nat)
    (hrow : rowCount < UInt32.size) (hdict : dictionaryBytes < UInt32.size) :
    decodePrefix (byteArrayOfList (writeU32LE magic ++ [version] ++
        writeU32LE (UInt32.ofNat rowCount) ++ writeU32LE (UInt32.ofNat dictionaryBytes)))
      = some { rowCount := rowCount, dictionaryBytes := dictionaryBytes } := by
  have hmagic : readU32LE (writeU32LE magic ++ [version] ++
      writeU32LE (UInt32.ofNat rowCount) ++ writeU32LE (UInt32.ofNat dictionaryBytes)) 0
      = some magic := by
    rw [show writeU32LE magic ++ [version] ++ writeU32LE (UInt32.ofNat rowCount) ++
          writeU32LE (UInt32.ofNat dictionaryBytes)
        = writeU32LE magic ++ ([version] ++ writeU32LE (UInt32.ofNat rowCount) ++
          writeU32LE (UInt32.ofNat dictionaryBytes)) by simp [List.append_assoc]]
    exact readU32LE_writeU32LE_append _ _
  have hdrop : (writeU32LE magic ++ [version] ++ writeU32LE (UInt32.ofNat rowCount) ++
      writeU32LE (UInt32.ofNat dictionaryBytes)).drop 4
      = version :: (writeU32LE (UInt32.ofNat rowCount) ++
        writeU32LE (UInt32.ofNat dictionaryBytes)) := by
    simp [writeU32LE]
  have hr0 : readU32LE (writeU32LE (UInt32.ofNat rowCount) ++
      writeU32LE (UInt32.ofNat dictionaryBytes)) 0 = some (UInt32.ofNat rowCount) :=
    readU32LE_writeU32LE_append _ _
  have hr4 : readU32LE (writeU32LE (UInt32.ofNat rowCount) ++
      writeU32LE (UInt32.ofNat dictionaryBytes)) 4 = some (UInt32.ofNat dictionaryBytes) := by
    rw [show writeU32LE (UInt32.ofNat rowCount) ++ writeU32LE (UInt32.ofNat dictionaryBytes)
        = writeU32LE (UInt32.ofNat rowCount) ++
          writeU32LE (UInt32.ofNat dictionaryBytes) ++ [] by simp,
      show (4 : Nat) = (writeU32LE (UInt32.ofNat rowCount)).length by simp]
    exact readU32LE_append_writeU32LE _ _ _
  rw [decodePrefix, listOfByteArray_byteArrayOfList]
  simp only [hmagic, hdrop, bind, Option.bind, parseU8, bne_self_eq_false,
    Bool.false_eq_true, if_false, hr0, hr4,
    u32_toNat_ofNat_of_lt hrow, u32_toNat_ofNat_of_lt hdict]

/-! ## The IBK3 round trip -/

/-- Whatever `encode?` accepts, `decode` restores with the same dictionary
    array and the same ID row array, so the two blocks denote the same graph.

`hfit` is not redundant with the `encode?` guards. PTD1 inside IBK3 calls the
TOTAL term encoder `serializeTerm`, which writes a truncated u32 length prefix
for a string of `2 ^ 32` bytes or more; no guard sees that, and
`L4Factoidal.Storage.termFitsU32` is what excludes it.

`hnodup` and `hwf` are the two `IndexedBlock.fromParts?` admission conditions
that `encode?` does not check. `fromParts?` refuses a dictionary with repeated
terms, because its ID map would not be injective; and it refuses rows whose IDs
do not resolve to an RDF subject, predicate IRI and object. A `Block` built by
`IndexedBlock.fromGraph` satisfies both, but the `Block` structure itself
carries no such invariant, so they are stated.

`BlockWireV0.termSupported`, the four `fitsU32` row and count guards, and
`onePredicate` are all inside `encode?`'s own `supported` gate, so they are
read out of `h` rather than assumed. -/
theorem decode_encode? (block : Block)
    (hfit : ∀ t ∈ block.dict.toList, termFitsU32 t)
    (hnodup : block.dict.toList.Nodup)
    (hwf : block.rows.toList.all (IndexedBlock.rowWellFormed block.dict) = true)
    (bytes : ByteArray) (h : encode? block = some bytes) :
    ∃ decoded, decode bytes = some decoded ∧
      decoded.dict = block.dict ∧ decoded.rows = block.rows := by
  rw [encode?] at h
  split at h
  · exact absurd h (by simp)
  · rename_i hsupp
    cases hdict : PagedTermDictionary.encode? block.dict with
    | none => rw [hdict] at h; exact absurd h (by simp)
    | some dictionary =>
      rw [hdict] at h
      simp only [bind, Option.bind] at h
      split at h
      · exact absurd h (by simp)
      · rename_i hguard
        injection h with h
        subst h
        -- the admission conditions `encode?` already checked
        have hu32 : (4294967296 : Nat) = UInt32.size := rfl
        have hsup : supported block = true := by simpa using hsupp
        simp only [supported, IndexedBlockWireV1.supported, IndexedBlockWireV1.fitsU32,
          PagedTermDictionary.supported, PagedTermDictionary.fitsU32,
          Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hsup
        have hterms : ∀ t ∈ block.dict.toList, BlockWireV0.termSupported t = true :=
          hsup.1.1.1.1.1
        have hnfit : block.rows.size < UInt32.size := hu32 ▸ hsup.1.1.1.2
        have honep : onePredicate block = true := hsup.1.2
        have hrowbounds : ∀ row ∈ block.rows.toList, row.s < UInt32.size ∧
            row.p < UInt32.size ∧ row.o < UInt32.size := by
          intro row hrow
          obtain ⟨⟨hs, hp⟩, ho⟩ := hsup.1.1.2 row hrow
          exact ⟨hu32 ▸ hs, hu32 ▸ hp, hu32 ▸ ho⟩
        simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_le] at hguard
        have hdfit : dictionary.size < UInt32.size := hguard.1
        -- the byte object the encoder built
        obtain ⟨rowsList, hrowsList⟩ : ∃ r, r = List.flatMap encodeRow (positionedRows block) :=
          ⟨_, rfl⟩
        rw [← hrowsList]
        obtain ⟨pay, hpay⟩ : ∃ p, p = writeU32LE (UInt32.ofNat block.rows.size) ++
          writeU32LE (UInt32.ofNat dictionary.size) ++ rowsList ++ dictionary.data.toList :=
          ⟨_, rfl⟩
        rw [← hpay]
        obtain ⟨inp, hinp⟩ : ∃ i, i = writeU32LE magic ++ [version] ++ pay ++
          writeU32LE (crc32c pay) := ⟨_, rfl⟩
        rw [← hinp]
        obtain ⟨pre13, hpre13⟩ : ∃ q, q = writeU32LE magic ++ [version] ++
          writeU32LE (UInt32.ofNat block.rows.size) ++
          writeU32LE (UInt32.ofNat dictionary.size) := ⟨_, rfl⟩
        -- lengths
        have hposLen : (positionedRows block).length = block.rows.size := by
          rw [positionedRows_eq]; simp
        have hrowsLen : rowsList.length = block.rows.size * 16 := by
          rw [hrowsList, flatMap_encodeRow_length, hposLen]
        have hdictLen : dictionary.data.toList.length = dictionary.size := by
          simp only [ByteArray.size, Array.length_toList]
        have hpayLen : pay.length = 8 + block.rows.size * 16 + dictionary.size := by
          rw [hpay]
          simp only [List.length_append, writeU32LE_length, hrowsLen, hdictLen]
        have hinpLen : inp.length = 17 + block.rows.size * 16 + dictionary.size := by
          rw [hinp]
          simp only [List.length_append, writeU32LE_length, List.length_cons,
            List.length_nil, hpayLen]
          omega
        have hpre13Len : pre13.length = 13 := by rw [hpre13]; simp
        -- four framings of the same byte list
        have hsplitA : inp = pre13 ++ (rowsList ++ (dictionary.data.toList ++
            writeU32LE (crc32c pay))) := by
          rw [hinp, hpre13, hpay]; simp [List.append_assoc]
        have hsplitB : inp = (pre13 ++ rowsList) ++ (dictionary.data.toList ++
            writeU32LE (crc32c pay)) := by rw [hsplitA, List.append_assoc]
        have hsplitC : inp = (writeU32LE magic ++ [version]) ++
            (pay ++ writeU32LE (crc32c pay)) := by rw [hinp]; simp [List.append_assoc]
        have hsplitD : inp = (writeU32LE magic ++ [version] ++ pay) ++
            (writeU32LE (crc32c pay) ++ []) := by rw [hinp]; simp [List.append_assoc]
        -- the header decodes to the counts the encoder wrote
        have hex13 : (byteArrayOfList inp).extract 0 prefixBytes = byteArrayOfList pre13 := by
          rw [extract_byteArrayOfList]
          congr 1
          rw [List.drop_zero, hsplitA]
          exact List.take_left' (by simp [hpre13Len, prefixBytes])
        have hheader : decodePrefix ((byteArrayOfList inp).extract 0 prefixBytes)
            = some { rowCount := block.rows.size, dictionaryBytes := dictionary.size } := by
          rw [hex13, hpre13]
          exact decodePrefix_ok block.rows.size dictionary.size hnfit hdfit
        -- the payload the decoder hashes is the payload the encoder hashed
        have hpayex : (inp.drop magicVersionBytes).take
            (inp.length - magicVersionBytes - crcBytes) = pay := by
          rw [hinpLen, hsplitC, List.drop_left' (by simp [magicVersionBytes])]
          exact List.take_left' (by
            rw [hpayLen]; simp only [magicVersionBytes, crcBytes]; omega)
        have hcrc : readU32LE inp (inp.length - crcBytes) = some (crc32c pay) := by
          rw [hinpLen, hsplitD,
            show 17 + block.rows.size * 16 + dictionary.size - crcBytes
              = (writeU32LE magic ++ [version] ++ pay).length by
              simp only [List.length_append, writeU32LE_length, List.length_cons,
                List.length_nil, hpayLen, crcBytes]
              omega]
          exact PagedTermDictionary.readU32LE_at_prefix _ _ _
        -- the row and dictionary areas are the byte ranges the encoder laid out
        have hrowsex : (byteArrayOfList inp).extract prefixBytes
            (prefixBytes + block.rows.size * rowBytes) = byteArrayOfList rowsList := by
          rw [extract_byteArrayOfList]
          congr 1
          rw [show prefixBytes + block.rows.size * rowBytes - prefixBytes
              = block.rows.size * rowBytes by omega, hsplitA,
            List.drop_left' (by simp only [hpre13Len, prefixBytes])]
          exact List.take_left' (by rw [hrowsLen]; simp only [rowBytes])
        have hdictex : (byteArrayOfList inp).extract (prefixBytes + block.rows.size * rowBytes)
            (prefixBytes + block.rows.size * rowBytes + dictionary.size) = dictionary := by
          rw [extract_byteArrayOfList,
            show prefixBytes + block.rows.size * rowBytes + dictionary.size -
              (prefixBytes + block.rows.size * rowBytes) = dictionary.size by omega]
          have hslice : (inp.drop (prefixBytes + block.rows.size * rowBytes)).take dictionary.size
              = dictionary.data.toList := by
            rw [hsplitB, List.drop_left' (by
              simp only [List.length_append, hpre13Len, hrowsLen, prefixBytes, rowBytes])]
            exact List.take_left' hdictLen
          rw [hslice]
          exact byteArrayOfList_listOfByteArray dictionary
        -- the rows round trip
        have hbound : ∀ entry ∈ positionedRows block, entry.position < UInt32.size ∧
            entry.row.s < UInt32.size ∧ entry.row.p < UInt32.size ∧
            entry.row.o < UInt32.size := by
          intro entry hentry
          rw [positionedRows_eq] at hentry
          obtain ⟨hrow, hpos⟩ := mem_map_positioned block.rows.toList 0 entry hentry
          obtain ⟨hs, hp, ho⟩ := hrowbounds entry.row hrow
          refine ⟨Nat.lt_trans ?_ hnfit, hs, hp, ho⟩
          simpa using hpos
        have hdecrows : decodeRows block.rows.size (byteArrayOfList rowsList)
            = some (positionedRows block) := by
          rw [decodeRows, if_neg (by
            rw [size_byteArrayOfList, hrowsLen]; simp [rowBytes])]
          have hgo := decodeRowsGo_ok (positionedRows block) [] [] hbound
          simp only [List.nil_append, List.length_nil, List.reverse_nil] at hgo
          rw [← hrowsList, hposLen] at hgo
          exact hgo
        -- the dictionary round trips
        obtain ⟨ptdHeader, hptdPrefix, hptdPage⟩ :=
          ptd_pageTerms_of_encode? block.dict dictionary hdict
        have hptddec : PagedTermDictionary.decode? dictionary = some block.dict :=
          PagedTermDictionary.decode?_encode? block.dict hterms hfit dictionary hdict
        obtain ⟨decoded, hparts, hddict, hdrows⟩ := fromParts?_ok block.dict block.rows hnodup hwf
        refine ⟨decoded, ?_, hddict, hdrows⟩
        -- assemble
        rw [decode, listOfByteArray_byteArrayOfList]
        simp only [hheader, bind, Option.bind]
        rw [if_neg (by rw [hinpLen]; simp only [prefixBytes, rowBytes]; omega), hpayex, hcrc]
        simp only [bne_self_eq_false, Bool.false_eq_true, if_false]
        have hend : prefixBytes + block.rows.size * rowBytes + dictionary.size + 4
            = inp.length := by
          rw [hinpLen]; simp only [prefixBytes, rowBytes]; omega
        rw [hend, bne_self_eq_false]
        simp only [Bool.false_eq_true, if_false]
        rw [hdictex, hptdPrefix]
        simp only [bind, Option.bind, hptdPage, bne_self_eq_false, Bool.false_eq_true, if_false]
        rw [hrowsex, hdecrows]
        simp only [bind, Option.bind]
        rw [orderedRows?_positionedRows]
        simp only [bind, Option.bind, predicateLocal_rows, honep, Bool.not_true,
          Bool.false_eq_true, if_false, hptddec]
        exact hparts

/-- The graph an IBK3 artifact denotes is the graph its source block denotes.
    `IndexedBlock.Block.denotes` reads only the dictionary array and the row
    array, which `decode_encode?` restores unchanged. -/
theorem denotes_decode_encode? (block : Block)
    (hfit : ∀ t ∈ block.dict.toList, termFitsU32 t)
    (hnodup : block.dict.toList.Nodup)
    (hwf : block.rows.toList.all (IndexedBlock.rowWellFormed block.dict) = true)
    (bytes : ByteArray) (h : encode? block = some bytes) :
    ∃ decoded, decode bytes = some decoded ∧ decoded.denotes = block.denotes := by
  obtain ⟨decoded, hdec, hddict, hdrows⟩ := decode_encode? block hfit hnodup hwf bytes h
  exact ⟨decoded, hdec, by rw [Block.denotes, Block.denotes, hddict, hdrows]⟩

#print axioms decodePrefix_ok
#print axioms decodeRowsGo_ok
#print axioms fromParts?_ok
#print axioms ptd_pageTerms_of_encode?
#print axioms decode_encode?
#print axioms denotes_decode_encode?

end L4Factoidal.Storage.IndexedBlockWireV3
