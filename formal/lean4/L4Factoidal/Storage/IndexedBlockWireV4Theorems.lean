/-
L4Factoidal.Storage.IndexedBlockWireV4Theorems — the round-trip proof for the
IBK4 quad-block codec of `L4Factoidal.Storage.IndexedBlockWireV4`.

IBK4 writes a seventeen-byte header, then the fixed-width graph-set summary,
then fixed-width twenty-byte quad rows, then a complete PTD1 paged term
dictionary, then a CRC32C over every post-version byte. `decode` reads all of
that back, re-checks the framing, the row order, the predicate locality and the
graph-set summary against the decoded rows, and rebuilds a block through
`IndexedBlockWireV4.fromParts?`. This module proves the two agree:

    encode? block = some bytes →
      ∃ decoded, decode bytes = some decoded ∧
        decoded.dict = block.dict ∧ decoded.rows = block.rows

`QuadBlock` also carries two hash maps, which `fromParts?` rebuilds from the
dictionary and the rows, so block equality is not the statement. The two array
fields are what `QuadBlock.denotes` reads, and `denotes_decode_encode?` draws
the quad-level corollary from them: the decoded artifact denotes the same list
of quads `(g, s, p, o)`, with `g = none` for the default graph.

The layering is IBK3's, with two additions. `decodeGraphsGo_ok` is the graph
summary's own fixed-width walk, and it needs `graphOfField_graphField`, the
inverse property of the biased graph column (wire `0` is the default graph,
wire `k + 1` is local ID `k`). `decodeRowsGo_ok` reads five fields per row
rather than four. The byte-array bridge, the `readU32At?` lemma and the PTD1
page-size lemma are IBK3's and are reused, not restated.

There is no hypothesis beyond `encode? block = some bytes`. Every check
`decode` performs is discharged from `encode?`'s own `supported` gate and its
three size guards. In particular `supported` runs
`(fromParts? block.dict block.rows).isSome`, the decoder's own reconstruction
step, which refuses a dictionary with repeated terms and any row whose
subject, predicate, object or GRAPH ID does not resolve.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.IndexedBlockWireV4
import L4Factoidal.Storage.IndexedBlockWireV3Theorems

namespace L4Factoidal.Storage.IndexedBlockWireV4

open L4Factoidal.RDF
open L4Factoidal.Storage
open L4Factoidal.Storage.IndexedBlock (buildIdMap)
open L4Factoidal.Storage.IndexedBlockWireV3 (byteArrayOfList listOfByteArray readU32At?
  size_byteArrayOfList listOfByteArray_byteArrayOfList byteArrayOfList_listOfByteArray
  extract_byteArrayOfList readU32At?_byteArrayOfList readU32At?_at
  ptd_pageTerms_of_encode?)

/-! ## Positioned rows -/

/-- The pairing `positionedRows` applies to each source row and its index. -/
def positioned (pair : IdQuad × Nat) : PositionedIdQuad :=
  { position := pair.2, row := pair.1 }

/-- `positionedRows` is that pairing mapped over the indexed row list. -/
theorem positionedRows_eq (block : QuadBlock) :
    positionedRows block = block.rows.toList.zipIdx.map positioned := rfl

/-- Every encoded row occupies twenty bytes. -/
theorem encodeRow_length (entry : PositionedIdQuad) : (encodeRow entry).length = 20 := by
  simp [encodeRow]

/-- A row list encodes to twenty bytes per row. -/
theorem flatMap_encodeRow_length : ∀ (rows : List PositionedIdQuad),
    (rows.flatMap encodeRow).length = rows.length * 20 := by
  intro rows
  induction rows with
  | nil => simp
  | cons entry rest ih =>
      simp only [List.flatMap_cons, List.length_append, encodeRow_length, ih,
        List.length_cons]
      omega

/-- Every graph-set entry occupies four bytes. -/
theorem flatMap_encodeGraphEntry_length : ∀ (graphs : List (Option IndexedBlock.TermId)),
    (graphs.flatMap encodeGraphEntry).length = graphs.length * 4 := by
  intro graphs
  induction graphs with
  | nil => simp
  | cons g rest ih =>
      simp only [List.flatMap_cons, List.length_append, encodeGraphEntry,
        writeU32LE_length, ih, List.length_cons]
      omega

/-- Positioning preserves the row list. -/
theorem map_row_map_positioned : ∀ (rows : List IdQuad) (start : Nat),
    ((rows.zipIdx start).map positioned).map PositionedIdQuad.row = rows := by
  intro rows
  induction rows with
  | nil => intro start; simp
  | cons row rest ih =>
      intro start
      simp only [List.zipIdx_cons, List.map_cons, positioned, ih (start + 1)]

/-- A positioned row carries a source row and an index inside the declared
    row extent. -/
theorem mem_map_positioned : ∀ (rows : List IdQuad) (start : Nat)
    (entry : PositionedIdQuad), entry ∈ (rows.zipIdx start).map positioned →
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
theorem canonicalOrder_map_positioned : ∀ (rows : List IdQuad) (start : Nat),
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

/-! ## The graph-set summary -/

/-- The graph-set walk decodes every written entry back, in wire order. The
    bound is the summary conjunct of `fieldsSupported`. -/
theorem decodeGraphsGo_ok : ∀ (graphs : List (Option IndexedBlock.TermId))
    (pre : List UInt8) (reversed : List (Option IndexedBlock.TermId)),
    (∀ g ∈ graphs, graphField g < UInt32.size) →
    decodeGraphsGo graphs.length
        (byteArrayOfList (pre ++ graphs.flatMap encodeGraphEntry))
        pre.length reversed = some (reversed.reverse ++ graphs) := by
  intro graphs
  induction graphs with
  | nil => intro pre reversed _; simp [decodeGraphsGo]
  | cons g rest ih =>
      intro pre reversed hbound
      have hg := hbound g (by simp)
      have h0 : readU32At? (byteArrayOfList (pre ++ (g :: rest).flatMap encodeGraphEntry))
          pre.length = some (UInt32.ofNat (graphField g)) := by
        rw [show pre ++ (g :: rest).flatMap encodeGraphEntry
            = pre ++ writeU32LE (UInt32.ofNat (graphField g)) ++
              rest.flatMap encodeGraphEntry by
          simp [encodeGraphEntry, List.append_assoc]]
        exact readU32At?_at _ _ _
      have hval : graphOfField (UInt32.ofNat (graphField g)).toNat = g := by
        rw [u32_toNat_ofNat_of_lt hg, graphOfField_graphField]
      have hnext : pre ++ (g :: rest).flatMap encodeGraphEntry
          = (pre ++ encodeGraphEntry g) ++ rest.flatMap encodeGraphEntry := by
        simp [List.append_assoc]
      have hoff : pre.length + graphEntryBytes = (pre ++ encodeGraphEntry g).length := by
        simp [graphEntryBytes, encodeGraphEntry]
      rw [List.length_cons, decodeGraphsGo]
      simp only [h0, bind, Option.bind, hval]
      rw [hnext, hoff, ih (pre ++ encodeGraphEntry g) (g :: reversed)
        (fun x hx => hbound x (List.mem_cons_of_mem _ hx))]
      simp

/-! ## Fixed-width row decoding -/

/-- The row walk decodes every encoded row back, in wire order. The five bound
    conditions are the `fitsU32` guards of `fieldsSupported` together with the
    source position being inside the row extent. -/
theorem decodeRowsGo_ok : ∀ (rows : List PositionedIdQuad) (pre : List UInt8)
    (reversed : List PositionedIdQuad),
    (∀ entry ∈ rows, entry.position < UInt32.size ∧
      graphField entry.row.g < UInt32.size ∧ entry.row.s < UInt32.size ∧
      entry.row.p < UInt32.size ∧ entry.row.o < UInt32.size) →
    decodeRowsGo rows.length (byteArrayOfList (pre ++ rows.flatMap encodeRow))
        pre.length reversed = some (reversed.reverse ++ rows) := by
  intro rows
  induction rows with
  | nil => intro pre reversed _; simp [decodeRowsGo]
  | cons entry rest ih =>
      intro pre reversed hbound
      obtain ⟨hpos, hg, hs, hp, ho⟩ := hbound entry (by simp)
      have h0 : readU32At? (byteArrayOfList (pre ++ (entry :: rest).flatMap encodeRow))
          pre.length = some (UInt32.ofNat entry.position) := by
        rw [show pre ++ (entry :: rest).flatMap encodeRow
            = pre ++ writeU32LE (UInt32.ofNat entry.position) ++
              (writeU32LE (UInt32.ofNat (graphField entry.row.g)) ++
                writeU32LE (UInt32.ofNat entry.row.s) ++
                writeU32LE (UInt32.ofNat entry.row.p) ++
                writeU32LE (UInt32.ofNat entry.row.o) ++ rest.flatMap encodeRow) by
          simp [encodeRow, List.append_assoc]]
        exact readU32At?_at _ _ _
      have h1 : readU32At? (byteArrayOfList (pre ++ (entry :: rest).flatMap encodeRow))
          (pre.length + 4) = some (UInt32.ofNat (graphField entry.row.g)) := by
        rw [show pre ++ (entry :: rest).flatMap encodeRow
            = (pre ++ writeU32LE (UInt32.ofNat entry.position)) ++
              writeU32LE (UInt32.ofNat (graphField entry.row.g)) ++
              (writeU32LE (UInt32.ofNat entry.row.s) ++
                writeU32LE (UInt32.ofNat entry.row.p) ++
                writeU32LE (UInt32.ofNat entry.row.o) ++ rest.flatMap encodeRow) by
          simp [encodeRow, List.append_assoc],
          show pre.length + 4
            = (pre ++ writeU32LE (UInt32.ofNat entry.position)).length by simp]
        exact readU32At?_at _ _ _
      have h2 : readU32At? (byteArrayOfList (pre ++ (entry :: rest).flatMap encodeRow))
          (pre.length + 8) = some (UInt32.ofNat entry.row.s) := by
        rw [show pre ++ (entry :: rest).flatMap encodeRow
            = (pre ++ writeU32LE (UInt32.ofNat entry.position) ++
                writeU32LE (UInt32.ofNat (graphField entry.row.g))) ++
              writeU32LE (UInt32.ofNat entry.row.s) ++
              (writeU32LE (UInt32.ofNat entry.row.p) ++
                writeU32LE (UInt32.ofNat entry.row.o) ++ rest.flatMap encodeRow) by
          simp [encodeRow, List.append_assoc],
          show pre.length + 8
            = (pre ++ writeU32LE (UInt32.ofNat entry.position) ++
                writeU32LE (UInt32.ofNat (graphField entry.row.g))).length by simp]
        exact readU32At?_at _ _ _
      have h3 : readU32At? (byteArrayOfList (pre ++ (entry :: rest).flatMap encodeRow))
          (pre.length + 12) = some (UInt32.ofNat entry.row.p) := by
        rw [show pre ++ (entry :: rest).flatMap encodeRow
            = (pre ++ writeU32LE (UInt32.ofNat entry.position) ++
                writeU32LE (UInt32.ofNat (graphField entry.row.g)) ++
                writeU32LE (UInt32.ofNat entry.row.s)) ++
              writeU32LE (UInt32.ofNat entry.row.p) ++
              (writeU32LE (UInt32.ofNat entry.row.o) ++ rest.flatMap encodeRow) by
          simp [encodeRow, List.append_assoc],
          show pre.length + 12
            = (pre ++ writeU32LE (UInt32.ofNat entry.position) ++
                writeU32LE (UInt32.ofNat (graphField entry.row.g)) ++
                writeU32LE (UInt32.ofNat entry.row.s)).length by simp]
        exact readU32At?_at _ _ _
      have h4 : readU32At? (byteArrayOfList (pre ++ (entry :: rest).flatMap encodeRow))
          (pre.length + 16) = some (UInt32.ofNat entry.row.o) := by
        rw [show pre ++ (entry :: rest).flatMap encodeRow
            = (pre ++ writeU32LE (UInt32.ofNat entry.position) ++
                writeU32LE (UInt32.ofNat (graphField entry.row.g)) ++
                writeU32LE (UInt32.ofNat entry.row.s) ++
                writeU32LE (UInt32.ofNat entry.row.p)) ++
              writeU32LE (UInt32.ofNat entry.row.o) ++ rest.flatMap encodeRow by
          simp [encodeRow, List.append_assoc],
          show pre.length + 16
            = (pre ++ writeU32LE (UInt32.ofNat entry.position) ++
                writeU32LE (UInt32.ofNat (graphField entry.row.g)) ++
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
             row := { g := graphOfField (UInt32.ofNat (graphField entry.row.g)).toNat,
                      s := (UInt32.ofNat entry.row.s).toNat,
                      p := (UInt32.ofNat entry.row.p).toNat,
                      o := (UInt32.ofNat entry.row.o).toNat } } : PositionedIdQuad)
            = entry := by
        rw [u32_toNat_ofNat_of_lt hpos, u32_toNat_ofNat_of_lt hg,
          graphOfField_graphField, u32_toNat_ofNat_of_lt hs,
          u32_toNat_ofNat_of_lt hp, u32_toNat_ofNat_of_lt ho]
      rw [List.length_cons, decodeRowsGo]
      simp only [h0, h1, h2, h3, h4, bind, Option.bind, hentry]
      rw [hnext, hoff, ih (pre ++ encodeRow entry) (entry :: reversed)
        (fun e he => hbound e (List.mem_cons_of_mem _ he))]
      simp

/-! ## Row order and predicate locality -/

/-- The encoder writes rows in canonical position order. -/
theorem canonicalOrder_positionedRows (block : QuadBlock) :
    canonicalOrder (positionedRows block) = true := by
  rw [canonicalOrder, positionedRows_eq]
  exact canonicalOrder_map_positioned block.rows.toList 0

/-- Canonical rows are admitted by the direct path and restore the row array. -/
theorem orderedRows?_positionedRows (block : QuadBlock) :
    orderedRows? block.rows.size (positionedRows block) = some block.rows := by
  have hlen : (positionedRows block).length = block.rows.size := by
    rw [positionedRows_eq]; simp
  rw [orderedRows?, if_neg (by simp [hlen]), if_pos (canonicalOrder_positionedRows block),
    positionedRows_eq, map_row_map_positioned]

/-- The decoder's predicate-locality check is the encoder's admission check. -/
theorem predicateLocal_rows (block : QuadBlock) :
    predicateLocal block.rows = onePredicate block := rfl

/-! ## Dictionary identity reconstruction -/

/-- Whenever `fromParts?` returns a block at all, that block carries exactly
    the dictionary and rows it was given. The `isSome` premise is the last
    conjunct of `supported`, so the encoder runs the decoder's reconstruction
    admission — including the graph-ID resolution check — itself. -/
theorem fromParts?_ok (dict : Array Term) (rows : Array IdQuad)
    (hsome : (fromParts? dict rows).isSome = true) :
    ∃ decoded, fromParts? dict rows = some decoded ∧
      decoded.dict = dict ∧ decoded.rows = rows := by
  obtain ⟨decoded, hdec⟩ := Option.isSome_iff_exists.mp hsome
  refine ⟨decoded, hdec, ?_⟩
  rw [fromParts?] at hdec
  cases hids : buildIdMap dict.toList 0 ∅ with
  | none => rw [hids] at hdec; exact absurd hdec (by simp)
  | some ids =>
      rw [hids] at hdec
      simp only [bind, Option.bind] at hdec
      split at hdec
      · injection hdec with hdec
        subst hdec
        exact ⟨rfl, rfl⟩
      · exact absurd hdec (by simp)

/-! ## The fixed IBK4 header -/

/-- The seventeen-byte header decodes to the row count, dictionary byte length
    and distinct-graph count the encoder wrote. -/
theorem decodePrefix_ok (rowCount dictionaryBytes graphCount : Nat)
    (hrow : rowCount < UInt32.size) (hdict : dictionaryBytes < UInt32.size)
    (hgraph : graphCount < UInt32.size) :
    decodePrefix (byteArrayOfList (writeU32LE magic ++ [version] ++
        writeU32LE (UInt32.ofNat rowCount) ++ writeU32LE (UInt32.ofNat dictionaryBytes) ++
        writeU32LE (UInt32.ofNat graphCount)))
      = some { rowCount := rowCount, dictionaryBytes := dictionaryBytes,
               graphCount := graphCount } := by
  have hmagic : readU32LE (writeU32LE magic ++ [version] ++
      writeU32LE (UInt32.ofNat rowCount) ++ writeU32LE (UInt32.ofNat dictionaryBytes) ++
      writeU32LE (UInt32.ofNat graphCount)) 0 = some magic := by
    rw [show writeU32LE magic ++ [version] ++ writeU32LE (UInt32.ofNat rowCount) ++
          writeU32LE (UInt32.ofNat dictionaryBytes) ++ writeU32LE (UInt32.ofNat graphCount)
        = writeU32LE magic ++ ([version] ++ writeU32LE (UInt32.ofNat rowCount) ++
          writeU32LE (UInt32.ofNat dictionaryBytes) ++
          writeU32LE (UInt32.ofNat graphCount)) by simp [List.append_assoc]]
    exact readU32LE_writeU32LE_append _ _
  have hdrop : (writeU32LE magic ++ [version] ++ writeU32LE (UInt32.ofNat rowCount) ++
      writeU32LE (UInt32.ofNat dictionaryBytes) ++ writeU32LE (UInt32.ofNat graphCount)).drop 4
      = version :: (writeU32LE (UInt32.ofNat rowCount) ++
        writeU32LE (UInt32.ofNat dictionaryBytes) ++ writeU32LE (UInt32.ofNat graphCount)) := by
    simp [writeU32LE]
  have hr0 : readU32LE (writeU32LE (UInt32.ofNat rowCount) ++
      writeU32LE (UInt32.ofNat dictionaryBytes) ++ writeU32LE (UInt32.ofNat graphCount)) 0
      = some (UInt32.ofNat rowCount) := by
    rw [show writeU32LE (UInt32.ofNat rowCount) ++ writeU32LE (UInt32.ofNat dictionaryBytes) ++
          writeU32LE (UInt32.ofNat graphCount)
        = writeU32LE (UInt32.ofNat rowCount) ++ (writeU32LE (UInt32.ofNat dictionaryBytes) ++
          writeU32LE (UInt32.ofNat graphCount)) by simp [List.append_assoc]]
    exact readU32LE_writeU32LE_append _ _
  have hr4 : readU32LE (writeU32LE (UInt32.ofNat rowCount) ++
      writeU32LE (UInt32.ofNat dictionaryBytes) ++ writeU32LE (UInt32.ofNat graphCount)) 4
      = some (UInt32.ofNat dictionaryBytes) := by
    rw [show (4 : Nat) = (writeU32LE (UInt32.ofNat rowCount)).length by simp]
    exact readU32LE_append_writeU32LE _ _ _
  have hr8 : readU32LE (writeU32LE (UInt32.ofNat rowCount) ++
      writeU32LE (UInt32.ofNat dictionaryBytes) ++ writeU32LE (UInt32.ofNat graphCount)) 8
      = some (UInt32.ofNat graphCount) := by
    rw [show writeU32LE (UInt32.ofNat rowCount) ++ writeU32LE (UInt32.ofNat dictionaryBytes) ++
          writeU32LE (UInt32.ofNat graphCount)
        = writeU32LE (UInt32.ofNat rowCount) ++ writeU32LE (UInt32.ofNat dictionaryBytes) ++
          writeU32LE (UInt32.ofNat graphCount) ++ [] by simp,
      show (8 : Nat) = (writeU32LE (UInt32.ofNat rowCount) ++
          writeU32LE (UInt32.ofNat dictionaryBytes)).length by simp]
    exact readU32LE_append_writeU32LE _ _ _
  rw [decodePrefix, listOfByteArray_byteArrayOfList]
  simp only [hmagic, hdrop, bind, Option.bind, parseU8, bne_self_eq_false,
    Bool.false_eq_true, if_false, hr0, hr4, hr8,
    u32_toNat_ofNat_of_lt hrow, u32_toNat_ofNat_of_lt hdict,
    u32_toNat_ofNat_of_lt hgraph]

/-! ## The IBK4 round trip -/

/-- Whatever `encode?` accepts, `decode` restores with the same dictionary
    array and the same ID quad row array, so the two blocks denote the same
    list of quads. The only hypothesis is that `encode?` accepted the block.

Every check `decode` performs is a consequence of `encode?`'s own `supported`
gate and its three size guards. `BlockWireV0.termSupported` and the `fitsU32`
row, count and graph-column guards come from `fieldsSupported`; the
predicate-locality check from `onePredicate`; `L4Factoidal.Storage.termFitsU32`
from `PagedTermDictionary.supported`; and the two `fromParts?` admission
conditions — a dictionary without repeated terms, and rows whose subject,
predicate, object and graph IDs resolve — from the
`(fromParts? block.dict block.rows).isSome` conjunct, which is the decoder's
reconstruction step run on the encoder's own inputs. The graph-set summary
needs no separate condition: the encoder writes `distinctGraphs` of the rows
and the decoder recomputes `distinctGraphs` of the rows it decoded. -/
theorem decode_encode? (block : QuadBlock)
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
        have hfits1 : ∀ n : Nat, IndexedBlockWireV1.fitsU32 n = true → n < UInt32.size := by
          intro n hn
          simp only [IndexedBlockWireV1.fitsU32, decide_eq_true_eq] at hn
          exact hu32 ▸ hn
        have hsup : supported block = true := by simpa using hsupp
        rw [supported, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hsup
        obtain ⟨⟨⟨hfields, honep⟩, hptd⟩, hpartsSome⟩ := hsup
        rw [fieldsSupported, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
          Bool.and_eq_true, List.all_eq_true, List.all_eq_true, List.all_eq_true] at hfields
        obtain ⟨⟨⟨⟨-, -⟩, hrowcount⟩, hrowfields⟩, hgraphfields⟩ := hfields
        have hnfit : block.rows.size < UInt32.size := hfits1 _ hrowcount
        have hrowbounds : ∀ row ∈ block.rows.toList, graphField row.g < UInt32.size ∧
            row.s < UInt32.size ∧ row.p < UInt32.size ∧ row.o < UInt32.size := by
          intro row hrow
          have hall := hrowfields row hrow
          rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hall
          exact ⟨hfits1 _ hall.2, hfits1 _ hall.1.1.1, hfits1 _ hall.1.1.2, hfits1 _ hall.1.2⟩
        have hgraphbounds : ∀ g ∈ distinctGraphs block.rows.toList,
            graphField g < UInt32.size := fun g hg => hfits1 _ (hgraphfields g hg)
        -- PTD1 admission: the decodable term subset and the u32 length-prefix test
        rw [PagedTermDictionary.supported, Bool.and_eq_true, List.all_eq_true] at hptd
        simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_le] at hguard
        have hdfit : dictionary.size < UInt32.size := hguard.1.1
        have hgfit : (distinctGraphs block.rows.toList).length < UInt32.size := hguard.2
        -- the byte object the encoder built
        obtain ⟨graphs, hgraphs⟩ : ∃ g, g = distinctGraphs block.rows.toList := ⟨_, rfl⟩
        rw [← hgraphs] at hgfit hgraphbounds ⊢
        obtain ⟨graphBytes, hgraphBytes⟩ : ∃ g, g = List.flatMap encodeGraphEntry graphs :=
          ⟨_, rfl⟩
        rw [← hgraphBytes]
        obtain ⟨rowsList, hrowsList⟩ : ∃ r, r = List.flatMap encodeRow (positionedRows block) :=
          ⟨_, rfl⟩
        rw [← hrowsList]
        obtain ⟨pay, hpay⟩ : ∃ p, p = writeU32LE (UInt32.ofNat block.rows.size) ++
          writeU32LE (UInt32.ofNat dictionary.size) ++
          writeU32LE (UInt32.ofNat graphs.length) ++ graphBytes ++ rowsList ++
          dictionary.data.toList := ⟨_, rfl⟩
        rw [← hpay]
        obtain ⟨inp, hinp⟩ : ∃ i, i = writeU32LE magic ++ [version] ++ pay ++
          writeU32LE (crc32c pay) := ⟨_, rfl⟩
        rw [← hinp]
        obtain ⟨pre17, hpre17⟩ : ∃ q, q = writeU32LE magic ++ [version] ++
          writeU32LE (UInt32.ofNat block.rows.size) ++
          writeU32LE (UInt32.ofNat dictionary.size) ++
          writeU32LE (UInt32.ofNat graphs.length) := ⟨_, rfl⟩
        -- lengths
        have hposLen : (positionedRows block).length = block.rows.size := by
          rw [positionedRows_eq]; simp
        have hrowsLen : rowsList.length = block.rows.size * 20 := by
          rw [hrowsList, flatMap_encodeRow_length, hposLen]
        have hgraphLen : graphBytes.length = graphs.length * 4 := by
          rw [hgraphBytes, flatMap_encodeGraphEntry_length]
        have hdictLen : dictionary.data.toList.length = dictionary.size := by
          simp only [ByteArray.size, Array.length_toList]
        have hpayLen : pay.length
            = 12 + graphs.length * 4 + block.rows.size * 20 + dictionary.size := by
          rw [hpay]
          simp only [List.length_append, writeU32LE_length, hgraphLen, hrowsLen, hdictLen]
        have hinpLen : inp.length
            = 21 + graphs.length * 4 + block.rows.size * 20 + dictionary.size := by
          rw [hinp]
          simp only [List.length_append, writeU32LE_length, List.length_cons,
            List.length_nil, hpayLen]
          omega
        have hpre17Len : pre17.length = 17 := by rw [hpre17]; simp
        -- five framings of the same byte list
        have hsplitA : inp = pre17 ++ (graphBytes ++ (rowsList ++ (dictionary.data.toList ++
            writeU32LE (crc32c pay)))) := by
          rw [hinp, hpre17, hpay]; simp [List.append_assoc]
        have hsplitB : inp = (pre17 ++ graphBytes) ++ (rowsList ++ (dictionary.data.toList ++
            writeU32LE (crc32c pay))) := by rw [hsplitA, List.append_assoc]
        have hsplitC : inp = (pre17 ++ graphBytes ++ rowsList) ++ (dictionary.data.toList ++
            writeU32LE (crc32c pay)) := by rw [hinp, hpre17, hpay]; simp [List.append_assoc]
        have hsplitD : inp = (writeU32LE magic ++ [version]) ++
            (pay ++ writeU32LE (crc32c pay)) := by rw [hinp]; simp [List.append_assoc]
        have hsplitE : inp = (writeU32LE magic ++ [version] ++ pay) ++
            (writeU32LE (crc32c pay) ++ []) := by rw [hinp]; simp [List.append_assoc]
        -- the header decodes to the counts the encoder wrote
        have hex17 : (byteArrayOfList inp).extract 0 prefixBytes = byteArrayOfList pre17 := by
          rw [extract_byteArrayOfList]
          congr 1
          rw [List.drop_zero, hsplitA]
          exact List.take_left' (by simp [hpre17Len, prefixBytes])
        have hheader : decodePrefix ((byteArrayOfList inp).extract 0 prefixBytes)
            = some { rowCount := block.rows.size, dictionaryBytes := dictionary.size,
                     graphCount := graphs.length } := by
          rw [hex17, hpre17]
          exact decodePrefix_ok block.rows.size dictionary.size graphs.length hnfit hdfit hgfit
        -- the payload the decoder hashes is the payload the encoder hashed
        have hpayex : (inp.drop magicVersionBytes).take
            (inp.length - magicVersionBytes - crcBytes) = pay := by
          rw [hinpLen, hsplitD, List.drop_left' (by simp [magicVersionBytes])]
          exact List.take_left' (by
            rw [hpayLen]; simp only [magicVersionBytes, crcBytes]; omega)
        have hcrc : readU32LE inp (inp.length - crcBytes) = some (crc32c pay) := by
          rw [hinpLen, hsplitE,
            show 21 + graphs.length * 4 + block.rows.size * 20 + dictionary.size - crcBytes
              = (writeU32LE magic ++ [version] ++ pay).length by
              simp only [List.length_append, writeU32LE_length, List.length_cons,
                List.length_nil, hpayLen, crcBytes]
              omega]
          exact PagedTermDictionary.readU32LE_at_prefix _ _ _
        -- the three variable-width areas are the byte ranges the encoder laid out
        have hgraphex : (byteArrayOfList inp).extract prefixBytes
            (prefixBytes + graphs.length * graphEntryBytes) = byteArrayOfList graphBytes := by
          rw [extract_byteArrayOfList]
          congr 1
          rw [show prefixBytes + graphs.length * graphEntryBytes - prefixBytes
              = graphs.length * graphEntryBytes by omega, hsplitA,
            List.drop_left' (by simp only [hpre17Len, prefixBytes])]
          exact List.take_left' (by rw [hgraphLen]; simp only [graphEntryBytes])
        have hrowsex : (byteArrayOfList inp).extract
            (prefixBytes + graphs.length * graphEntryBytes)
            (prefixBytes + graphs.length * graphEntryBytes + block.rows.size * rowBytes)
            = byteArrayOfList rowsList := by
          rw [extract_byteArrayOfList]
          congr 1
          rw [show prefixBytes + graphs.length * graphEntryBytes +
              block.rows.size * rowBytes - (prefixBytes + graphs.length * graphEntryBytes)
              = block.rows.size * rowBytes by omega, hsplitB,
            List.drop_left' (by
              simp only [List.length_append, hpre17Len, hgraphLen, prefixBytes, graphEntryBytes])]
          exact List.take_left' (by rw [hrowsLen]; simp only [rowBytes])
        have hdictex : (byteArrayOfList inp).extract
            (prefixBytes + graphs.length * graphEntryBytes + block.rows.size * rowBytes)
            (prefixBytes + graphs.length * graphEntryBytes + block.rows.size * rowBytes +
              dictionary.size) = dictionary := by
          rw [extract_byteArrayOfList,
            show prefixBytes + graphs.length * graphEntryBytes + block.rows.size * rowBytes +
              dictionary.size - (prefixBytes + graphs.length * graphEntryBytes +
              block.rows.size * rowBytes) = dictionary.size by omega]
          have hslice : (inp.drop (prefixBytes + graphs.length * graphEntryBytes +
              block.rows.size * rowBytes)).take dictionary.size = dictionary.data.toList := by
            rw [hsplitC, List.drop_left' (by
              simp only [List.length_append, hpre17Len, hgraphLen, hrowsLen, prefixBytes,
                graphEntryBytes, rowBytes])]
            exact List.take_left' hdictLen
          rw [hslice]
          exact byteArrayOfList_listOfByteArray dictionary
        -- the graph-set summary round trips
        have hdecgraphs : decodeGraphSummary graphs.length (byteArrayOfList graphBytes)
            = some graphs := by
          rw [decodeGraphSummary, if_neg (by
            rw [size_byteArrayOfList, hgraphLen]; simp [graphEntryBytes])]
          have hgo := decodeGraphsGo_ok graphs [] [] hgraphbounds
          simp only [List.nil_append, List.length_nil, List.reverse_nil] at hgo
          rw [← hgraphBytes] at hgo
          exact hgo
        -- the rows round trip
        have hbound : ∀ entry ∈ positionedRows block, entry.position < UInt32.size ∧
            graphField entry.row.g < UInt32.size ∧ entry.row.s < UInt32.size ∧
            entry.row.p < UInt32.size ∧ entry.row.o < UInt32.size := by
          intro entry hentry
          rw [positionedRows_eq] at hentry
          obtain ⟨hrow, hpos⟩ := mem_map_positioned block.rows.toList 0 entry hentry
          obtain ⟨hg, hs, hp, ho⟩ := hrowbounds entry.row hrow
          refine ⟨Nat.lt_trans ?_ hnfit, hg, hs, hp, ho⟩
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
          PagedTermDictionary.decode?_encode? block.dict dictionary hdict
        obtain ⟨decoded, hparts, hddict, hdrows⟩ :=
          fromParts?_ok block.dict block.rows hpartsSome
        refine ⟨decoded, ?_, hddict, hdrows⟩
        -- assemble
        rw [decode, listOfByteArray_byteArrayOfList]
        simp only [hheader, bind, Option.bind]
        rw [if_neg (by
          rw [hinpLen]; simp only [prefixBytes, graphEntryBytes, rowBytes]; omega),
          hpayex, hcrc]
        simp only [bne_self_eq_false, Bool.false_eq_true, if_false]
        have hend : prefixBytes + graphs.length * graphEntryBytes +
            block.rows.size * rowBytes + dictionary.size + 4 = inp.length := by
          rw [hinpLen]; simp only [prefixBytes, graphEntryBytes, rowBytes]; omega
        rw [hend, bne_self_eq_false]
        simp only [Bool.false_eq_true, if_false]
        rw [hdictex, hptdPrefix]
        simp only [bind, Option.bind, hptdPage, bne_self_eq_false, Bool.false_eq_true, if_false]
        rw [hgraphex, hdecgraphs]
        simp only [bind, Option.bind]
        rw [hrowsex, hdecrows]
        simp only [bind, Option.bind]
        rw [orderedRows?_positionedRows]
        simp only [bind, Option.bind, predicateLocal_rows, honep, Bool.not_true,
          Bool.false_eq_true, if_false]
        rw [← hgraphs, bne_self_eq_false]
        simp only [Bool.false_eq_true, if_false, hptddec]
        exact hparts

/-- The quads an IBK4 artifact denotes are the quads its source block denotes.
    `QuadBlock.denotes` reads only the dictionary array and the row array,
    which `decode_encode?` restores unchanged. -/
theorem denotes_decode_encode? (block : QuadBlock)
    (bytes : ByteArray) (h : encode? block = some bytes) :
    ∃ decoded, decode bytes = some decoded ∧ decoded.denotes = block.denotes := by
  obtain ⟨decoded, hdec, hddict, hdrows⟩ := decode_encode? block bytes h
  exact ⟨decoded, hdec, by rw [QuadBlock.denotes, QuadBlock.denotes, hddict, hdrows]⟩

#print axioms decodePrefix_ok
#print axioms decodeGraphsGo_ok
#print axioms decodeRowsGo_ok
#print axioms fromParts?_ok
#print axioms decode_encode?
#print axioms denotes_decode_encode?

end L4Factoidal.Storage.IndexedBlockWireV4
