/-
L4Factoidal.Storage.IndexedBlockWireV5Theorems — the round-trip proof for the
IBK5 quad-block codec of `L4Factoidal.Storage.IndexedBlockWireV5`.

IBK5 writes a seventeen-byte header, then the fixed-width graph-set summary,
then fixed-width twenty-byte quad rows, then a complete PTD2 paged term
dictionary, then a CRC32C over every post-version byte. `decode` reads all of
that back, re-checks the framing, the row order, the predicate locality and the
graph-set summary against the decoded rows, and rebuilds a block through
`IndexedBlockWireV5.fromParts?`. This module proves the two agree:

    encode? block = some bytes →
      ∃ decoded, decode bytes = some decoded ∧
        decoded.dict = block.dict ∧ decoded.rows = block.rows

and draws the wire-quad corollary `denotes_decode_encode?` and the RDF-quad
corollary `resolveBlock_decode_encode?` from it.

The graph-summary and row fields are IBK4's, so their walk lemmas
(`decodeGraphsGo_ok`, `decodeRowsGo_ok`, the `positioned` lemmas and the
payload-slice lemma) are `IndexedBlockWireV4Theorems`'s and are reused, not
restated. The paged dictionary is PTD2, so its round trip and its declared
page size come from the generic `PTD` theorems at
`PagedTermDictionaryV2.v2Format` — the same theorems PTD1 uses.

There is no hypothesis beyond `encode? block = some bytes`.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.IndexedBlockWireV5
import L4Factoidal.Storage.IndexedBlockWireV4Theorems
import L4Factoidal.Storage.PagedTermDictionaryV2Theorems

namespace L4Factoidal.Storage.IndexedBlockWireV5

open L4Factoidal.RDF
open L4Factoidal.Storage
open L4Factoidal.Storage.TermWireV2
open L4Factoidal.Storage.IndexedBlockWireV3 (byteArrayOfList listOfByteArray readU32At?
  size_byteArrayOfList listOfByteArray_byteArrayOfList byteArrayOfList_listOfByteArray
  extract_byteArrayOfList readU32At?_byteArrayOfList readU32At?_at)
open L4Factoidal.Storage.IndexedBlockWireV4 (IdQuad PositionedIdQuad graphField graphOfField
  distinctGraphs encodeRow encodeGraphEntry canonicalOrder predicateLocal
  graphEntryBytes rowBytes prefixBytes magicVersionBytes crcBytes
  decodeGraphSummary decodeRows orderedRows?
  positioned map_row_map_positioned
  mem_map_positioned canonicalOrder_map_positioned flatMap_encodeRow_length
  flatMap_encodeGraphEntry_length decodeGraphsGo_ok decodeRowsGo_ok)

/-! ## Positioned rows -/

/-- `positionedRows` is IBK4's pairing mapped over the indexed row list. -/
theorem positionedRows_eq (block : QuadBlock) :
    positionedRows block = block.rows.toList.zipIdx.map positioned := rfl

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

/-- Whenever `fromParts?` returns a block at all, that block carries exactly
    the dictionary and rows it was given. The `isSome` premise is the last
    conjunct of `supported`, so the encoder runs the decoder's reconstruction
    admission — including the graph-ID resolution check — itself. -/
theorem fromParts?_ok (dict : Array WireTerm) (rows : Array IdQuad)
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

/-- Whatever `encode?` accepts, `decode` restores with the same dictionary
    array and the same ID quad row array, so the two blocks denote the same
    list of quads. The only hypothesis is that `encode?` accepted the block.

Every check `decode` performs is a consequence of `encode?`'s own `supported`
gate and its three size guards. The v2 term-codec admission and the `fitsU32`
row, count and graph-column guards come from `fieldsSupported`; the
predicate-locality check from `onePredicate`; the dictionary-wide
admission from `PagedTermDictionaryV2.supported`; and the two `fromParts?` admission
conditions — a dictionary without repeated terms, and rows whose subject,
predicate, object and graph IDs resolve — from the
`(fromParts? block.dict block.rows).isSome` conjunct, which is the decoder's
reconstruction step run on the encoder's own inputs. The graph-set summary
needs no separate condition: the encoder writes `distinctGraphs` of the rows
and the decoder recomputes `distinctGraphs` of the rows it decoded. -/
theorem decodeSpec_encode? (block : QuadBlock)
    (bytes : ByteArray) (h : encode? block = some bytes) :
    ∃ decoded, decodeSpec bytes = some decoded ∧
      decoded.dict = block.dict ∧ decoded.rows = block.rows := by
  rw [encode?] at h
  split at h
  · exact absurd h (by simp)
  · rename_i hsupp
    cases hdict : PagedTermDictionaryV2.encode? block.dict with
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
        obtain ⟨⟨⟨hfields, honep⟩, -⟩, hpartsSome⟩ := hsup
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
          exact PTD.readU32LE_at_prefix _ _ _
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
          PagedTermDictionaryV2.pageTerms_of_encode? block.dict dictionary hdict
        have hptddec : PagedTermDictionaryV2.decode? dictionary = some block.dict :=
          PagedTermDictionaryV2.decode?_encode? block.dict dictionary hdict
        obtain ⟨decoded, hparts, hddict, hdrows⟩ :=
          fromParts?_ok block.dict block.rows hpartsSome
        refine ⟨decoded, ?_, hddict, hdrows⟩
        -- assemble
        rw [decodeSpec, listOfByteArray_byteArrayOfList]
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

/-- The in-place decoder admits exactly the bytes the specification admits, and
    returns exactly the block it returns. -/
theorem decode_eq_spec (bytes : ByteArray) : decode bytes = decodeSpec bytes := by
  simp only [decode, decodeSpec,
    IndexedBlockWireV3.length_listOfByteArray,
    IndexedBlockWireV3.readU32LE_listOfByteArray,
    IndexedBlockWireV4.crc32c_payload_slice_v4]

/-- Whatever `encode?` accepts, `decode` restores with the same dictionary
    array and the same ID quad row array. -/
theorem decode_encode? (block : QuadBlock)
    (bytes : ByteArray) (h : encode? block = some bytes) :
    ∃ decoded, decode bytes = some decoded ∧
      decoded.dict = block.dict ∧ decoded.rows = block.rows := by
  rw [decode_eq_spec]
  exact decodeSpec_encode? block bytes h

/-- The quads an IBK5 artifact denotes are the quads its source block denotes.
    `QuadBlock.denotes` reads only the dictionary array and the row array,
    which `decode_encode?` restores unchanged. -/
theorem denotes_decode_encode? (block : QuadBlock)
    (bytes : ByteArray) (h : encode? block = some bytes) :
    ∃ decoded, decode bytes = some decoded ∧ decoded.denotes = block.denotes := by
  obtain ⟨decoded, hdec, hddict, hdrows⟩ := decode_encode? block bytes h
  exact ⟨decoded, hdec, by rw [QuadBlock.denotes, QuadBlock.denotes, hddict, hdrows]⟩

/-! ## Resolution back to RDF quads

`resolveBlock` reads only `QuadBlock.denotes`, which `decode_encode?` restores
unchanged, so the decoded artifact resolves to whatever the source block
resolves to. The second theorem closes the loop to RDF: a block whose
denotation is the wire form of a quad list, written and read back, resolves to
that quad list.

`hlookup` is the packer's obligation and `TermWireV2.resolve_toWire` is what
discharges it: for one quad the literal's own bytes resolve its own object,
which is `resolve_toWire_object` below. A real reader supplies one lookup over
the manifest blob table; that lookup satisfies `hlookup` exactly when it
returns each named digest's bytes. -/

/-- The decoded artifact resolves to whatever the source block resolves to,
for any hash function and any lookup. -/
theorem resolveBlock_decode_encode? (h : ByteArray → ByteArray)
    (lookup : ByteArray → Option ByteArray) (block : QuadBlock) (bytes : ByteArray)
    (henc : encode? block = some bytes) :
    ∃ decoded, decode bytes = some decoded ∧
      resolveBlock h lookup decoded = resolveBlock h lookup block := by
  obtain ⟨decoded, hdec, hden⟩ := denotes_decode_encode? block bytes henc
  exact ⟨decoded, hdec, by rw [resolveBlock, resolveBlock, hden]⟩

/-- The packer's own lookup resolves one quad's object. -/
theorem resolve_toWire_object (h : ByteArray → ByteArray)
    (quad : Option GraphRef × Triple) :
    resolve h (lookupOf h quad.2.o) (toWire h quad.2.o) = some quad.2.o :=
  resolve_toWire h quad.2.o

private theorem mapM_toWireQuad (h : ByteArray → ByteArray)
    (lookup : ByteArray → Option ByteArray) :
    ∀ (quads : List (Option GraphRef × Triple)),
      (∀ q ∈ quads, resolve h lookup (toWire h q.2.o) = some q.2.o) →
      ((quads.map (toWireQuad h)).mapM fun quad => do
          let o ← resolve h lookup quad.2.o
          some (quad.1, ({ s := quad.2.s, p := quad.2.p, o := o } : Triple)))
        = some quads := by
  intro quads
  induction quads with
  | nil => intro _; rfl
  | cons q rest ih =>
      intro hlk
      have hq : resolve h lookup (toWire h q.2.o) = some q.2.o := hlk q (by simp)
      have hrest := ih (fun x hx => hlk x (by simp [hx]))
      simp only [List.map_cons, List.mapM_cons, toWireQuad, hq, hrest]
      rfl

/-- Resolving the decoded encoding of a block built by `toWire` from RDF quads
gives those quads back. `hdenotes` is the interning step: the block's wire-level
denotation is the wire form of the quads. `hlookup` is the blob obligation: the
lookup returns bytes that resolve each object. -/
theorem resolveBlock_decode_encode?_toWire (h : ByteArray → ByteArray)
    (lookup : ByteArray → Option ByteArray) (block : QuadBlock) (bytes : ByteArray)
    (quads : List (Option GraphRef × Triple))
    (henc : encode? block = some bytes)
    (hdenotes : block.denotes = quads.map (toWireQuad h))
    (hlookup : ∀ q ∈ quads, resolve h lookup (toWire h q.2.o) = some q.2.o) :
    ∃ decoded, decode bytes = some decoded ∧
      resolveBlock h lookup decoded = some quads := by
  obtain ⟨decoded, hdec, hres⟩ := resolveBlock_decode_encode? h lookup block bytes henc
  refine ⟨decoded, hdec, ?_⟩
  rw [hres, resolveBlock, hdenotes]
  exact mapM_toWireQuad h lookup quads hlookup

#print axioms positionedRows_eq
#print axioms fromParts?_ok
#print axioms decodePrefix_ok
#print axioms decodeSpec_encode?
#print axioms decode_eq_spec
#print axioms decode_encode?
#print axioms denotes_decode_encode?
#print axioms resolveBlock_decode_encode?
#print axioms resolve_toWire_object
#print axioms resolveBlock_decode_encode?_toWire

end L4Factoidal.Storage.IndexedBlockWireV5
