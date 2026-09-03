/-
L4Factoidal.Storage.TermLocalIndexWireTheorems — the round-trip proof for the
TLI1 term-to-local-ID codec of `L4Factoidal.Storage.TermLocalIndexWire`.

TLI1 writes a fifty-seven byte prefix (magic, version, the target IBK3
SHA-256 and five u32 counts), a directory of length-delimited page references,
pages of length-delimited entries, and a CRC32C over every post-version byte.
`decode?` reads all of that back and re-checks the prefix relations, the
directory framing and contiguity, the per-page entry count and first key, and
the global entry ordering and local-ID permutation. This module proves the two
agree:

    encode? index = some bytes → decode? bytes = some index

on the subset `encode?` admits, with no further hypothesis.

`decodeSpec?` works on the byte LIST throughout, so the bridge for the
round-trip proof is only `listOfByteArray (byteArrayOfList xs) = xs` and its
converse. `decode?` reads the same artifact by byte-array index, and
`decode?_eq_spec` proves the two are the same function, so the round-trip
theorems below are stated about `decode?` and proved through that equality.
The pagination
lemmas give `chunks` its four properties: it partitions the entry list, its
page count is the ceiling division the prefix records, its i-th page is the
i-th window of `pageTerms` entries, and no page is empty. `refsFrom` restates
`pageRefs` as a recursion with a running offset, which makes the contiguity
and coverage checks provable by induction. `parseEntry_encodeEntry` inverts
one entry through `L4Factoidal.Storage.parseTerm_serializeTerm`,
`parseEntries_ok` lifts that to a page, and `decodePages_ok` lifts that to the
page list under its directory.

Three conditions `decode?` enforces were not implied by the old `supported`:
`localIdsPermutation`, which `canonicalEntries` re-runs and which key ordering
does not imply, and the two admission conditions of the term codec round trip,
`termSupported` and `termFitsU32b`, which `parseEntry` needs to rebuild the RDF
term. Per the encoder-boundary policy `supported` now runs all three, so
`encode?` refuses exactly the indexes `decode?` would refuse and the theorem
below needs no extra hypothesis.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.TermLocalIndexWire
import L4Factoidal.Storage.TermCodecTheorems

namespace L4Factoidal.Storage.TermLocalIndexWire

open L4Factoidal.RDF
open L4Factoidal.Storage
open L4Factoidal.Storage.BlockWireV0
open L4Factoidal.Storage.TermLocalIndex

/-! ## Byte array bridge -/

/-- Reading a built byte array back gives the list it was built from. -/
theorem listOfByteArray_byteArrayOfList (xs : List UInt8) :
    listOfByteArray (byteArrayOfList xs) = xs := by
  simp [byteArrayOfList, listOfByteArray]

/-- Building from a byte array's own list returns that byte array. -/
theorem byteArrayOfList_listOfByteArray (b : ByteArray) :
    byteArrayOfList (listOfByteArray b) = b := by
  simp [byteArrayOfList, listOfByteArray]

/-- The same, in the spelling the encoder uses for the SHA-256 field. -/
theorem byteArrayOfList_data_toList (b : ByteArray) : byteArrayOfList b.data.toList = b :=
  byteArrayOfList_listOfByteArray b

/-- A byte array's list has its size. -/
theorem length_listOfByteArray (b : ByteArray) : (listOfByteArray b).length = b.size := by
  rw [listOfByteArray, Array.length_toList]
  rfl

/-- A four-byte field is readable at the length of the framing before it. -/
theorem readU32LE_at_prefix (pre : List UInt8) (n : UInt32) (rest : List UInt8) :
    readU32LE (pre ++ (writeU32LE n ++ rest)) pre.length = some n := by
  rw [← List.append_assoc]
  exact readU32LE_append_writeU32LE pre n rest

/-- The exact-length reader consumes a known prefix and leaves the rest. -/
theorem takeExact_append (xs rest : List UInt8) (n : Nat) (h : xs.length = n) :
    takeExact n (xs ++ rest) = some (xs, rest) := by
  rw [takeExact]
  simp only [List.take_left' h, List.drop_left' h, h, beq_self_eq_true, if_true]

/-! ## Pagination -/

/-- The recursive step of `chunks` on a nonempty list. -/
theorem chunks_cons {α : Type} (f : Nat) (a : α) (t : List α) :
    chunks (f + 1) (a :: t)
      = (a :: t).take pageTerms :: chunks f ((a :: t).drop pageTerms) := by
  rw [chunks]
  simp

/-- With enough fuel the pages partition the entry list. -/
theorem chunks_flatten {α : Type} : ∀ (f : Nat) (L : List α), L.length ≤ f →
    (chunks f L).flatten = L := by
  intro f
  induction f with
  | zero =>
      intro L hlen
      have hnil : L = [] := List.length_eq_zero_iff.mp (by omega)
      subst hnil; simp [chunks]
  | succ f ih =>
      intro L hlen
      match L with
      | [] => simp [chunks]
      | a :: t =>
          have hsub : ((a :: t).drop pageTerms).length ≤ f := by
            simp only [List.length_drop, List.length_cons, pageTerms]
            simp only [List.length_cons] at hlen
            omega
          rw [chunks_cons, List.flatten_cons, ih ((a :: t).drop pageTerms) hsub]
          exact List.take_append_drop pageTerms (a :: t)

/-- The page count is the ceiling division the prefix records. -/
theorem chunks_length {α : Type} : ∀ (f : Nat) (L : List α), L.length ≤ f →
    (chunks f L).length = (L.length + pageTerms - 1) / pageTerms := by
  intro f
  induction f with
  | zero =>
      intro L hlen
      have hnil : L = [] := List.length_eq_zero_iff.mp (by omega)
      subst hnil; simp [chunks, pageTerms]
  | succ f ih =>
      intro L hlen
      match L with
      | [] => simp [chunks, pageTerms]
      | a :: t =>
          have hsub : ((a :: t).drop pageTerms).length ≤ f := by
            simp only [List.length_drop, List.length_cons, pageTerms]
            simp only [List.length_cons] at hlen
            omega
          rw [chunks_cons, List.length_cons, ih ((a :: t).drop pageTerms) hsub]
          simp only [List.length_drop, List.length_cons, pageTerms]
          omega

/-- The i-th page is the i-th window of `pageTerms` entries. -/
theorem chunks_getElem? {α : Type} : ∀ (f : Nat) (L : List α) (j : Nat), L.length ≤ f →
    j < (L.length + pageTerms - 1) / pageTerms →
    (chunks f L)[j]? = some ((L.drop (j * pageTerms)).take pageTerms) := by
  intro f
  induction f with
  | zero =>
      intro L j hlen hj
      have hnil : L = [] := List.length_eq_zero_iff.mp (by omega)
      subst hnil; simp [pageTerms] at hj
  | succ f ih =>
      intro L j hlen hj
      match L with
      | [] => simp [pageTerms] at hj
      | a :: t =>
          have hsub : ((a :: t).drop pageTerms).length ≤ f := by
            simp only [List.length_drop, List.length_cons, pageTerms]
            simp only [List.length_cons] at hlen
            omega
          rw [chunks_cons]
          match j with
          | 0 => simp
          | k + 1 =>
              have hk : k < (((a :: t).drop pageTerms).length + pageTerms - 1) / pageTerms := by
                simp only [List.length_drop, List.length_cons, pageTerms]
                simp only [List.length_cons, pageTerms] at hj
                omega
              rw [List.getElem?_cons_succ, ih ((a :: t).drop pageTerms) k hsub hk,
                List.drop_drop]
              congr 3
              simp only [pageTerms]
              omega

/-- No page is empty, which is what makes the directory contiguous. -/
theorem chunks_ne_nil {α : Type} : ∀ (f : Nat) (L : List α) (pg : List α),
    pg ∈ chunks f L → pg ≠ [] := by
  intro f
  induction f with
  | zero => intro L pg hmem; simp [chunks] at hmem
  | succ f ih =>
      intro L pg hmem
      match L with
      | [] => simp [chunks] at hmem
      | a :: t =>
          rw [chunks_cons, List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · simp [pageTerms]
          · exact ih _ _ hmem

/-! ## The page directory -/

/-- The first key of a page, without an `Inhabited Entry` instance. -/
def headKey : List Entry → List UInt8
  | [] => []
  | e :: _ => e.key

/-- Each encoded entry is at least eight bytes, so no page is empty. -/
theorem encodeEntry_length (e : Entry) : (encodeEntry e).length = 8 + e.key.length := by
  simp only [encodeEntry, List.length_append, writeU32LE_length]
  omega

/-- A nonempty page has nonempty page bytes. -/
theorem flatMap_encodeEntry_pos : ∀ (page : List Entry), page ≠ [] →
    0 < (page.flatMap encodeEntry).length := by
  intro page hne
  match page, hne with
  | e :: rest, _ =>
      simp only [List.flatMap_cons, List.length_append, encodeEntry_length]
      omega

/-- The directory fold step, named so the accumulator lemma can be stated. -/
def refStep (state : Nat × List PageRef) (pair : List UInt8 × List Entry) :
    Nat × List PageRef :=
  let (offset, refs) := state
  let (bytes, page) := pair
  match page with
  | first :: _ => (offset + bytes.length,
      { firstKey := first.key, offset, length := bytes.length } :: refs)
  | [] => (offset, refs)

/-- `pageRefs` is that step folded over the zipped page lists. -/
theorem pageRefs_eq_fold (pages : List (List UInt8)) (entries : List (List Entry)) :
    pageRefs pages entries = ((pages.zip entries).foldl refStep (0, [])).2.reverse := rfl

/-- The directory as a recursion over pages with an explicit running offset. -/
def refsFrom : Nat → List (List Entry) → List PageRef
  | _, [] => []
  | base, page :: rest =>
      { firstKey := headKey page, offset := base,
        length := (page.flatMap encodeEntry).length } ::
        refsFrom (base + (page.flatMap encodeEntry).length) rest

/-- The directory fold accumulates a running offset and reversed entries. -/
theorem refStep_foldl : ∀ (EP : List (List Entry)) (base : Nat) (acc : List PageRef),
    (∀ p ∈ EP, p ≠ []) →
    ((EP.map (fun p => p.flatMap encodeEntry)).zip EP).foldl refStep (base, acc)
      = (base + (EP.map (fun p => (p.flatMap encodeEntry).length)).sum,
         (refsFrom base EP).reverse ++ acc) := by
  intro EP
  induction EP with
  | nil => intro base acc _; simp [refsFrom]
  | cons p EP' ih =>
      intro base acc hne
      have hp : p ≠ [] := hne p (by simp)
      match p, hp with
      | e :: t, _ =>
          rw [List.map_cons, List.zip_cons_cons, List.foldl_cons]
          have hstep : refStep (base, acc) ((e :: t).flatMap encodeEntry, e :: t)
              = (base + ((e :: t).flatMap encodeEntry).length,
                 { firstKey := headKey (e :: t), offset := base,
                   length := ((e :: t).flatMap encodeEntry).length } :: acc) := by
            simp only [refStep, headKey]
          rw [hstep, ih (base + ((e :: t).flatMap encodeEntry).length) _
            (fun q hq => hne q (by simp [hq]))]
          simp only [refsFrom, List.map_cons, List.sum_cons, List.reverse_cons,
            List.append_assoc, List.cons_append, List.nil_append]
          rw [Nat.add_assoc]

/-- `pageRefs` on the encoder's own page lists is `refsFrom` started at zero. -/
theorem pageRefs_eq (EP : List (List Entry)) (hne : ∀ p ∈ EP, p ≠ []) :
    pageRefs (EP.map (fun p => p.flatMap encodeEntry)) EP = refsFrom 0 EP := by
  rw [pageRefs_eq_fold, refStep_foldl EP 0 [] hne]
  simp

/-- One directory entry per page. -/
theorem refsFrom_length (EP : List (List Entry)) (base : Nat) :
    (refsFrom base EP).length = EP.length := by
  induction EP generalizing base with
  | nil => simp [refsFrom]
  | cons p rest ih => simp [refsFrom, ih]

/-- The coverage fold over the directory sums the page byte lengths. -/
theorem refsFrom_sum : ∀ (EP : List (List Entry)) (base start : Nat),
    (refsFrom base EP).foldl (fun total ref => total + ref.length) start
      = start + (EP.map (fun p => (p.flatMap encodeEntry).length)).sum := by
  intro EP
  induction EP with
  | nil => intro base start; simp [refsFrom]
  | cons p rest ih =>
      intro base start
      simp only [refsFrom, List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih (base + (p.flatMap encodeEntry).length)
        (start + (p.flatMap encodeEntry).length)]
      omega

/-- A directory of nonempty pages passes the contiguity check. -/
theorem refsContiguous_refsFrom : ∀ (EP : List (List Entry)) (base : Nat),
    (∀ p ∈ EP, p ≠ []) → refsContiguous (refsFrom base EP) base = true := by
  intro EP
  induction EP with
  | nil => intro base _; simp [refsFrom, refsContiguous]
  | cons p rest ih =>
      intro base hne
      have hpos : 0 < (p.flatMap encodeEntry).length :=
        flatMap_encodeEntry_pos p (hne p (by simp))
      rw [refsFrom, refsContiguous]
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, gt_iff_lt]
      exact ⟨⟨hpos, trivial⟩, ih (base + (p.flatMap encodeEntry).length)
        (fun q hq => hne q (by simp [hq]))⟩

/-- Every directory entry's key comes from the first entry of one page. -/
theorem refsFrom_mem : ∀ (EP : List (List Entry)) (base : Nat) (r : PageRef),
    r ∈ refsFrom base EP → ∃ p ∈ EP, r.firstKey = headKey p := by
  intro EP
  induction EP with
  | nil => intro base r hmem; simp [refsFrom] at hmem
  | cons p rest ih =>
      intro base r hmem
      rw [refsFrom, List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact ⟨p, by simp, rfl⟩
      · obtain ⟨q, hq, h⟩ := ih _ r hmem
        exact ⟨q, by simp [hq], h⟩

/-- Every directory entry lies inside the page area it describes. -/
theorem refsFrom_offset_bound : ∀ (EP : List (List Entry)) (base : Nat) (r : PageRef),
    r ∈ refsFrom base EP →
    r.offset + r.length ≤ base + (EP.map (fun p => (p.flatMap encodeEntry).length)).sum := by
  intro EP
  induction EP with
  | nil => intro base r hmem; simp [refsFrom] at hmem
  | cons p rest ih =>
      intro base r hmem
      rw [refsFrom, List.mem_cons] at hmem
      simp only [List.map_cons, List.sum_cons]
      rcases hmem with rfl | hmem
      · simp only []
        omega
      · have := ih (base + (p.flatMap encodeEntry).length) r hmem
        omega

/-! ## Entry bytes -/

/-- The admission conditions one entry must satisfy for `parseEntry` to
    rebuild it: its key is the canonical term serialization, the key and the
    local ID fit the u32 fields, and the term is inside the decodable subset
    the term codec round trip needs. -/
def entryOk (e : Entry) : Prop :=
  e.key = serializeTerm e.term ∧ e.key.length < UInt32.size ∧
    e.localId < UInt32.size ∧ termSupported e.term = true ∧ termFitsU32 e.term

/-- The entry decoder inverts `encodeEntry` and leaves the trailing bytes. -/
theorem parseEntry_encodeEntry (e : Entry) (rest : List UInt8) (h : entryOk e) :
    parseEntry (encodeEntry e ++ rest) = some (e, rest) := by
  obtain ⟨hkey, hklen, hid, hsup, hfit⟩ := h
  have e0 : encodeEntry e ++ rest
      = writeU32LE (UInt32.ofNat e.key.length) ++
        (e.key ++ (writeU32LE (UInt32.ofNat e.localId) ++ rest)) := by
    simp [encodeEntry, List.append_assoc]
  have hr0 : readU32LE (encodeEntry e ++ rest) 0
      = some (UInt32.ofNat e.key.length) := by
    rw [e0]
    exact readU32LE_writeU32LE_append _ _
  have hdrop : (encodeEntry e ++ rest).drop 4
      = e.key ++ (writeU32LE (UInt32.ofNat e.localId) ++ rest) := by
    rw [e0]
    exact List.drop_left' (by simp)
  have hterm : parseTerm e.key = some (e.term, []) := by
    rw [hkey, show serializeTerm e.term = serializeTerm e.term ++ [] by simp]
    exact parseTerm_serializeTerm e.term [] hsup hfit
  rw [parseEntry]
  simp only [hr0, bind, Option.bind, hdrop, u32_toNat_ofNat_of_lt hklen,
    takeExact_append e.key (writeU32LE (UInt32.ofNat e.localId) ++ rest) e.key.length rfl,
    readU32LE_writeU32LE_append, hterm, u32_toNat_ofNat_of_lt hid,
    List.isEmpty_nil, Bool.not_true, ← hkey, bne_self_eq_false, Bool.or_self,
    Bool.false_eq_true, if_false]
  rw [List.drop_left' (by simp : (writeU32LE (UInt32.ofNat e.localId)).length = 4)]

/-- A run of encoded entries decodes back, leaving the trailing bytes. -/
theorem parseEntries_ok : ∀ (page : List Entry) (rest : List UInt8) (rev : List Entry),
    (∀ e ∈ page, entryOk e) →
    parseEntries page.length (page.flatMap encodeEntry ++ rest) rev
      = some (rev.reverse ++ page, rest) := by
  intro page
  induction page with
  | nil => intro rest rev _; simp [parseEntries]
  | cons e page ih =>
      intro rest rev hok
      rw [List.length_cons, parseEntries,
        show (e :: page).flatMap encodeEntry ++ rest
          = encodeEntry e ++ (page.flatMap encodeEntry ++ rest) by simp [List.append_assoc],
        parseEntry_encodeEntry e _ (hok e (by simp))]
      simp only [bind, Option.bind]
      rw [ih rest (e :: rev) (fun x hx => hok x (by simp [hx]))]
      simp

/-! ## Directory bytes -/

/-- The reference decoder inverts `encodePageRef`. -/
theorem parseRef_encodePageRef (r : PageRef) (rest : List UInt8)
    (hk : r.firstKey.length < UInt32.size) (ho : r.offset < UInt32.size)
    (hl : r.length < UInt32.size) :
    parseRef (encodePageRef r ++ rest) = some (r, rest) := by
  have e0 : encodePageRef r ++ rest
      = writeU32LE (UInt32.ofNat r.firstKey.length) ++
        (r.firstKey ++ (writeU32LE (UInt32.ofNat r.offset) ++
          (writeU32LE (UInt32.ofNat r.length) ++ rest))) := by
    simp [encodePageRef, List.append_assoc]
  have hr0 : readU32LE (encodePageRef r ++ rest) 0
      = some (UInt32.ofNat r.firstKey.length) := by
    rw [e0]; exact readU32LE_writeU32LE_append _ _
  have hdrop : (encodePageRef r ++ rest).drop 4
      = r.firstKey ++ (writeU32LE (UInt32.ofNat r.offset) ++
        (writeU32LE (UInt32.ofNat r.length) ++ rest)) := by
    rw [e0]; exact List.drop_left' (by simp)
  have hr4 : readU32LE (writeU32LE (UInt32.ofNat r.offset) ++
      (writeU32LE (UInt32.ofNat r.length) ++ rest)) 4 = some (UInt32.ofNat r.length) := by
    rw [show (4 : Nat) = (writeU32LE (UInt32.ofNat r.offset)).length by simp]
    exact readU32LE_at_prefix _ _ _
  have hdrop8 : (writeU32LE (UInt32.ofNat r.offset) ++
      (writeU32LE (UInt32.ofNat r.length) ++ rest)).drop 8 = rest := by
    rw [← List.append_assoc]
    exact List.drop_left' (by simp)
  rw [parseRef]
  simp only [hr0, bind, Option.bind, hdrop, u32_toNat_ofNat_of_lt hk,
    takeExact_append r.firstKey _ r.firstKey.length rfl,
    readU32LE_writeU32LE_append, hr4, u32_toNat_ofNat_of_lt ho,
    u32_toNat_ofNat_of_lt hl, hdrop8]

/-- The directory decoder inverts `encodePageRef` entry by entry. -/
theorem parseRefs_ok : ∀ (R : List PageRef) (rest : List UInt8) (rev : List PageRef),
    (∀ r ∈ R, r.firstKey.length < UInt32.size ∧ r.offset < UInt32.size ∧
      r.length < UInt32.size) →
    parseRefs R.length (R.flatMap encodePageRef ++ rest) rev
      = some (rev.reverse ++ R, rest) := by
  intro R
  induction R with
  | nil => intro rest rev _; simp [parseRefs]
  | cons r R ih =>
      intro rest rev hb
      obtain ⟨hk, ho, hl⟩ := hb r (by simp)
      rw [List.length_cons, parseRefs,
        show (r :: R).flatMap encodePageRef ++ rest
          = encodePageRef r ++ (R.flatMap encodePageRef ++ rest) by simp [List.append_assoc],
        parseRef_encodePageRef r _ hk ho hl]
      simp only [bind, Option.bind]
      rw [ih rest (r :: rev) (fun x hx => hb x (by simp [hx]))]
      simp

/-! ## The page walk -/

/-- The page walk decodes every declared page and consumes the page area. -/
theorem decodePages_ok (termCount : Nat) :
    ∀ (EP : List (List Entry)) (i base : Nat) (rev : List Entry),
      (∀ p ∈ EP, p ≠ []) →
      (∀ p ∈ EP, ∀ e ∈ p, entryOk e) →
      (∀ j page, EP[j]? = some page → pageEntryCount termCount (i + j) = page.length) →
      decodePages termCount (refsFrom base EP)
          (EP.flatMap (fun p => p.flatMap encodeEntry)) i rev
        = some (rev.reverse ++ EP.flatten) := by
  intro EP
  induction EP with
  | nil => intro i base rev _ _ _; simp [refsFrom, decodePages]
  | cons p EP' ih =>
      intro i base rev hne hok hcount
      have hp : p ≠ [] := hne p (by simp)
      obtain ⟨first, t, hpc⟩ : ∃ a t, p = a :: t := by
        match p, hp with
        | a :: t, _ => exact ⟨a, t, rfl⟩
      subst hpc
      have hcount0 : pageEntryCount termCount i = (first :: t).length := by
        have := hcount 0 (first :: t) (by simp)
        simpa using this
      have hflat : ((first :: t) :: EP').flatMap (fun q => q.flatMap encodeEntry)
          = (first :: t).flatMap encodeEntry ++
            EP'.flatMap (fun q => q.flatMap encodeEntry) := by
        simp
      have htake : ((first :: t).flatMap encodeEntry ++
          EP'.flatMap (fun q => q.flatMap encodeEntry)).take
            ((first :: t).flatMap encodeEntry).length
          = (first :: t).flatMap encodeEntry := List.take_left' rfl
      have hdrop : ((first :: t).flatMap encodeEntry ++
          EP'.flatMap (fun q => q.flatMap encodeEntry)).drop
            ((first :: t).flatMap encodeEntry).length
          = EP'.flatMap (fun q => q.flatMap encodeEntry) := List.drop_left' rfl
      have hparse : parseEntries (pageEntryCount termCount i)
          ((first :: t).flatMap encodeEntry) [] = some (first :: t, []) := by
        rw [hcount0,
          show (first :: t).flatMap encodeEntry = (first :: t).flatMap encodeEntry ++ [] by simp,
          parseEntries_ok (first :: t) [] [] (hok (first :: t) (by simp))]
        simp
      rw [refsFrom, hflat, decodePages]
      simp only [htake, bne_self_eq_false, Bool.false_eq_true, if_false, hparse,
        bind, Option.bind, List.isEmpty_nil, Bool.not_true, headKey,
        bne_self_eq_false, hdrop]
      rw [ih (i + 1) (base + ((first :: t).flatMap encodeEntry).length)
        ((first :: t).reverse ++ rev)
        (fun q hq => hne q (by simp [hq]))
        (fun q hq => hok q (by simp [hq]))
        (fun j page hj => by
          have := hcount (j + 1) page (by simpa using hj)
          rw [← this]
          congr 1
          omega)]
      simp

/-! ## Whole-object round trip -/

/-- `pageBytes` is `chunks` at the default page size, entry-encoded. -/
theorem pageBytes_eq (es : List Entry) :
    pageBytes es = (chunks es.length es).map (fun p => p.flatMap encodeEntry) := rfl

/-- Flattening a map is the corresponding `flatMap`. -/
theorem flatten_map_eq_flatMap {α β : Type} (l : List α) (f : α → List β) :
    (l.map f).flatten = l.flatMap f := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih]

/-- A nonempty page's directory key is one of its entry keys. -/
theorem headKey_mem (p : List Entry) (h : p ≠ []) : ∃ e ∈ p, headKey p = e.key := by
  match p, h with
  | e :: t, _ => exact ⟨e, by simp, rfl⟩

/-! ## The byte-indexed decoder equals the list decoder

`decodeSpec?` is the list decoder and states what TLI1 admits. `decode?` reads
the same artifact by byte-array index. Everything below builds up to
`decode?_eq_spec`, which proves the two are the same function, so the
round-trip theorems and the activation decision are unchanged. -/

private theorem toListLoop_eq (b : ByteArray) :
    ∀ (fuel i : Nat) (r : List UInt8), b.size - i ≤ fuel →
      ByteArray.toList.loop b i r = r.reverse ++ b.data.toList.drop i := by
  intro fuel
  induction fuel with
  | zero =>
      intro i r h
      rw [ByteArray.toList.loop]
      have hnil : b.data.toList.drop i = [] := by
        apply List.drop_eq_nil_of_le
        simp only [Array.length_toList, ByteArray.size_data]
        omega
      rw [if_neg (by omega), hnil, List.append_nil]
  | succ fuel ih =>
      intro i r h
      rw [ByteArray.toList.loop]
      by_cases hlt : i < b.size
      · rw [if_pos hlt, ih (i + 1) _ (by omega)]
        have hlenList : i < b.data.toList.length := by
          simp only [Array.length_toList, ByteArray.size_data]; exact hlt
        rw [List.drop_eq_getElem_cons hlenList]
        have hget : b.get! i = b.data.toList[i] := by
          simp only [ByteArray.get!]
          exact getElem!_pos b.data i (by simpa using hlt)
        simp [hget]
      · rw [if_neg hlt]
        have hnil : b.data.toList.drop i = [] := by
          apply List.drop_eq_nil_of_le
          simp only [Array.length_toList, ByteArray.size_data]
          omega
        rw [hnil, List.append_nil]

/-- `ByteArray.toList` is the list of the packed data. -/
theorem toList_eq_listOfByteArray (b : ByteArray) : b.toList = listOfByteArray b := by
  have := toListLoop_eq b b.size 0 [] (by omega)
  simpa [ByteArray.toList, listOfByteArray] using this

/-- Building a byte array from an append is appending the two byte arrays. -/
theorem byteArrayOfList_append (xs ys : List UInt8) :
    byteArrayOfList (xs ++ ys) = byteArrayOfList xs ++ byteArrayOfList ys := by
  apply ByteArray.ext
  simp [byteArrayOfList]

/-- A byte-array extract is the corresponding list slice. -/
theorem listOfByteArray_extract (b : ByteArray) (i j : Nat) :
    listOfByteArray (b.extract i j) = ((listOfByteArray b).drop i).take (j - i) := by
  simp [listOfByteArray, ByteArray.data_extract, List.extract]

/-- Distinct byte lists build distinct byte arrays. -/
theorem byteArrayOfList_inj (xs ys : List UInt8) :
    byteArrayOfList xs = byteArrayOfList ys ↔ xs = ys := by
  constructor
  · intro h
    have := congrArg ByteArray.data h
    simpa [byteArrayOfList, ← Array.toList_inj] using this
  · intro h; rw [h]

private theorem byteArray_beq_eq (a b : ByteArray) : (a == b) = decide (a = b) := by
  show ByteArray.beq a b = _
  rw [ByteArray.beq]
  by_cases h : a.data = b.data
  · have hab : a = b := ByteArray.ext_iff.mpr h
    simp [hab]
  · have hab : a ≠ b := fun hx => h (by rw [hx])
    simp [h, hab]

theorem byteArrayOfList_beq (xs ys : List UInt8) :
    (byteArrayOfList xs == byteArrayOfList ys) = (xs == ys) := by
  rw [byteArray_beq_eq]
  by_cases h : xs = ys
  · subst h; simp
  · have hne : byteArrayOfList xs ≠ byteArrayOfList ys :=
      fun hb => h ((byteArrayOfList_inj _ _).mp hb)
    simp [h, hne]

/-! ### The packed term serialization -/

theorem serializeLStringBytes_eq (s : String) :
    serializeLStringBytes s = byteArrayOfList (serializeLString s) := by
  have hlist : bytesOfString s = listOfByteArray s.toUTF8 := toList_eq_listOfByteArray s.toUTF8
  have hpack : byteArrayOfList (bytesOfString s) = s.toUTF8 := by
    rw [hlist]; exact byteArrayOfList_listOfByteArray s.toUTF8
  have hlenStr : (bytesOfString s).length = s.toUTF8.size := by
    rw [hlist]; exact length_listOfByteArray s.toUTF8
  rw [serializeLString, serializeLStringBytes, byteArrayOfList_append, hlenStr, hpack]

/-- The packed serialization is the byte list `serializeTerm` writes, so the
    key check `parseEntryB` runs is the key check `parseEntry` runs. -/
theorem serializeTermBytes_eq (t : Term) :
    serializeTermBytes t = byteArrayOfList (serializeTerm t) := by
  cases t with
  | iri i => simp [serializeTermBytes, serializeTerm, serializeLStringBytes_eq,
      ← byteArrayOfList_append]
  | bnode b => simp [serializeTermBytes, serializeTerm, serializeLStringBytes_eq,
      ← byteArrayOfList_append]
  | literal l =>
      cases hlang : l.val.langTag with
      | none => simp [serializeTermBytes, serializeTerm, hlang, serializeLStringBytes_eq,
          ← byteArrayOfList_append]
      | some tag => simp [serializeTermBytes, serializeTerm, hlang, serializeLStringBytes_eq,
          ← byteArrayOfList_append]
  | tripleTerm a b c => simp [serializeTermBytes, serializeTerm]

theorem serializeTermBytes_bne (t : Term) (b : ByteArray) :
    (serializeTermBytes t != b) = (serializeTerm t != listOfByteArray b) := by
  rw [serializeTermBytes_eq]
  generalize hl : listOfByteArray b = xs
  have hb : b = byteArrayOfList xs := by rw [← hl, byteArrayOfList_listOfByteArray]
  rw [hb, bne, bne, byteArrayOfList_beq]

/-! ### Field reads -/

theorem readU32LEB_eq (bytes : ByteArray) (off : Nat) :
    readU32LEB bytes off = readU32LE (listOfByteArray bytes) off := by
  have hlenB : (listOfByteArray bytes).length = bytes.size := length_listOfByteArray bytes
  rw [readU32LEB]
  split
  · rename_i h
    have h0 : off < (listOfByteArray bytes).length := by omega
    have h1 : off + 1 < (listOfByteArray bytes).length := by omega
    have h2 : off + 2 < (listOfByteArray bytes).length := by omega
    have h3 : off + 3 < (listOfByteArray bytes).length := by omega
    simp only [readU32LE]
    rw [List.drop_eq_getElem_cons h0, List.drop_eq_getElem_cons h1,
      List.drop_eq_getElem_cons h2, List.drop_eq_getElem_cons h3]
    simp [listOfByteArray, ByteArray.getElem_eq_getElem_data]
  · rename_i h
    simp only [readU32LE]
    split
    · rename_i b0 b1 b2 b3 t heq
      have hl := congrArg List.length heq
      simp only [List.length_drop, hlenB, List.length_cons] at hl
      omega
    · rfl

theorem byteAtB_parseU8 (bytes : ByteArray) (off : Nat) :
    parseU8 ((listOfByteArray bytes).drop off)
      = (byteAtB bytes off).map (fun b => (b, (listOfByteArray bytes).drop (off + 1))) := by
  have hlenB : (listOfByteArray bytes).length = bytes.size := length_listOfByteArray bytes
  rw [byteAtB]
  split
  · rename_i h
    have h0 : off < (listOfByteArray bytes).length := by omega
    rw [List.drop_eq_getElem_cons h0]
    simp [parseU8, listOfByteArray, ByteArray.getElem_eq_getElem_data]
  · rename_i h
    have hnil : (listOfByteArray bytes).drop off = [] := by
      apply List.drop_eq_nil_of_le; omega
    simp [hnil, parseU8]

theorem readU32LE_drop_zero (l : List UInt8) (a : Nat) :
    readU32LE (l.drop a) 0 = readU32LE l a := by
  simp [readU32LE]

/-- A four-byte field can only be read where four bytes remain. -/
theorem readU32LE_bound (bytes : ByteArray) (off : Nat) (v : UInt32)
    (h : readU32LE (listOfByteArray bytes) off = some v) : off + 4 ≤ bytes.size := by
  have hlenB : (listOfByteArray bytes).length = bytes.size := length_listOfByteArray bytes
  rcases Nat.lt_or_ge bytes.size (off + 4) with hc | hc
  case inr => exact hc
  exfalso
  rw [readU32LE] at h
  split at h
  · rename_i b0 b1 b2 b3 t heq
    have hl := congrArg List.length heq
    simp only [List.length_drop, hlenB, List.length_cons] at hl
    omega
  · exact absurd h (by simp)

/-- Reading a field after a prefix drop is reading it at the sum offset. -/
theorem readU32LE_drop (l : List UInt8) (a k : Nat) :
    readU32LE (l.drop a) k = readU32LE l (a + k) := by
  simp [readU32LE, List.drop_drop]

/-- CRC32C of the artifact's own bytes, computed in place. -/
theorem crc32c_listOfByteArray (b : ByteArray) :
    crc32c (listOfByteArray b) = crc32cAppendArray 0xFFFFFFFF b ^^^ 0xFFFFFFFF := by
  rw [crc32c, crc32cAppendArray_eq]
  rfl

/-! ### Entries, pages and the page walk -/

theorem takeExactB (bytes : ByteArray) (start n : Nat) (hstart : start <= bytes.size) :
    takeExact n ((listOfByteArray bytes).drop start)
      = if start + n > bytes.size then none
        else some (listOfByteArray (bytes.extract start (start + n)),
                   (listOfByteArray bytes).drop (start + n)) := by
  have hlenB : (listOfByteArray bytes).length = bytes.size := length_listOfByteArray bytes
  have hslice : ((listOfByteArray bytes).drop start).take n
      = listOfByteArray (bytes.extract start (start + n)) := by
    rw [listOfByteArray_extract]
    simp
  have hrest : ((listOfByteArray bytes).drop start).drop n
      = (listOfByteArray bytes).drop (start + n) := by
    rw [List.drop_drop]
  rw [takeExact]
  simp only [hslice, hrest]
  by_cases h : start + n > bytes.size
  · rw [if_pos h]
    have : (listOfByteArray (bytes.extract start (start + n))).length != n := by
      rw [length_listOfByteArray, ByteArray.size_extract, Nat.min_def]
      simp only [bne_iff_ne, ne_eq]
      split <;> omega
    simp only [bne_iff_ne, ne_eq] at this
    simp [this]
  · rw [if_neg h]
    have : (listOfByteArray (bytes.extract start (start + n))).length = n := by
      rw [length_listOfByteArray, ByteArray.size_extract, Nat.min_def]
      split <;> omega
    simp [this]

private theorem someBind {a : Type} {b : Type} (x : a) (f : a -> Option b) :
    (some x >>= f) = f x := rfl

theorem parseEntryB_eq (bytes : ByteArray) (off : Nat) :
    (parseEntryB bytes off).map (fun p => (p.1, (listOfByteArray bytes).drop p.2))
      = parseEntry ((listOfByteArray bytes).drop off) := by
  simp only [parseEntryB, parseEntry, readU32LEB_eq, readU32LE_drop_zero]
  cases hkl : readU32LE (listOfByteArray bytes) off with
  | none => simp
  | some kl =>
      have hoff : off + 4 <= bytes.size := readU32LE_bound bytes off kl hkl
      have hdrop : ((listOfByteArray bytes).drop off).drop 4
          = (listOfByteArray bytes).drop (off + 4) := by rw [List.drop_drop]
      rw [someBind, someBind, hdrop, takeExactB bytes (off + 4) kl.toNat hoff]
      by_cases hfit : off + 4 + kl.toNat > bytes.size
      · simp [hfit]
      · simp only [if_neg hfit]
        simp only [someBind]
        simp only [readU32LE_drop_zero]
        simp only [serializeTermBytes_bne]
        cases hlid : readU32LE (listOfByteArray bytes) (off + 4 + kl.toNat) with
        | none => simp
        | some lid =>
            cases hterm : parseTerm (listOfByteArray
                (bytes.extract (off + 4) (off + 4 + kl.toNat))) with
            | none => simp
            | some pair =>
                simp only [someBind]
                split <;> simp

theorem parseEntryB_le (bytes : ByteArray) (off : Nat) (e : Entry) (next : Nat)
    (h : parseEntryB bytes off = some (e, next)) : next <= bytes.size := by
  simp only [parseEntryB] at h
  cases hkl : readU32LEB bytes off with
  | none => rw [hkl] at h; simp at h
  | some kl =>
      rw [hkl] at h
      simp only [someBind] at h
      by_cases hfit : off + 4 + kl.toNat > bytes.size
      · rw [if_pos hfit] at h; simp at h
      · rw [if_neg hfit] at h
        cases hlid : readU32LEB bytes (off + 4 + kl.toNat) with
        | none => rw [hlid] at h; simp at h
        | some lid =>
            have hb : off + 4 + kl.toNat + 4 <= bytes.size := by
              have hr := readU32LEB_eq bytes (off + 4 + kl.toNat)
              rw [hlid] at hr
              exact readU32LE_bound bytes _ lid hr.symm
            rw [hlid] at h
            simp only [someBind] at h
            cases hterm : parseTerm (listOfByteArray
                (bytes.extract (off + 4) (off + 4 + kl.toNat))) with
            | none => rw [hterm] at h; simp at h
            | some pair =>
                rw [hterm] at h
                simp only [someBind] at h
                split at h
                · simp at h
                · simp only [Option.some.injEq, Prod.mk.injEq] at h
                  omega

theorem parseEntriesB_eq (bytes : ByteArray) : ∀ (count off : Nat) (rev : List Entry),
    (parseEntriesB bytes count off rev).map (fun p => (p.1, (listOfByteArray bytes).drop p.2))
      = parseEntries count ((listOfByteArray bytes).drop off) rev := by
  intro count
  induction count with
  | zero => intro off rev; simp [parseEntriesB, parseEntries]
  | succ count ih =>
      intro off rev
      have hstep := parseEntryB_eq bytes off
      simp only [parseEntriesB, parseEntries]
      cases hp : parseEntryB bytes off with
      | none =>
          rw [hp] at hstep
          simp only [Option.map_none] at hstep
          rw [← hstep]
          simp
      | some pair =>
          obtain ⟨entry, next⟩ := pair
          rw [hp] at hstep
          simp only [Option.map_some] at hstep
          rw [← hstep]
          simp only [someBind]
          exact ih next (entry :: rev)

theorem parseEntriesB_le (bytes : ByteArray) : ∀ (count off : Nat) (rev es : List Entry)
    (next : Nat), off <= bytes.size → parseEntriesB bytes count off rev = some (es, next) →
      next <= bytes.size := by
  intro count
  induction count with
  | zero =>
      intro off rev es next hoff h
      simp only [parseEntriesB, Option.some.injEq, Prod.mk.injEq] at h
      omega
  | succ count ih =>
      intro off rev es next hoff h
      simp only [parseEntriesB] at h
      cases hp : parseEntryB bytes off with
      | none => rw [hp] at h; simp at h
      | some pair =>
          obtain ⟨entry, mid⟩ := pair
          have hmid : mid <= bytes.size := parseEntryB_le bytes off entry mid hp
          rw [hp] at h
          simp only [someBind] at h
          exact ih mid (entry :: rev) es next hmid h

theorem decodePagesB_eq (termCount : Nat) : ∀ (refs : List PageRef) (pages : ByteArray)
    (off page : Nat) (rev : List Entry), off <= pages.size →
      decodePagesB termCount refs pages off page rev
        = decodePages termCount refs ((listOfByteArray pages).drop off) page rev := by
  intro refs
  induction refs with
  | nil =>
      intro pages off page rev hoff
      have hlenP : (listOfByteArray pages).length = pages.size := length_listOfByteArray pages
      simp only [decodePagesB]
      by_cases heq : off = pages.size
      · have hnil : (listOfByteArray pages).drop off = [] := by
          apply List.drop_eq_nil_of_le; omega
        rw [hnil, if_pos (by simp [heq])]
        rfl
      · have hlt : off < (listOfByteArray pages).length := by omega
        rw [List.drop_eq_getElem_cons hlt, if_neg (by simp [heq])]
        rfl
  | cons ref rest ih =>
      intro pages off page rev hoff
      have hlenP : (listOfByteArray pages).length = pages.size := length_listOfByteArray pages
      have hslice : ((listOfByteArray pages).drop off).take ref.length
          = listOfByteArray (pages.extract off (off + ref.length)) := by
        rw [listOfByteArray_extract]; simp
      simp only [decodePagesB, decodePages, hslice]
      by_cases hfit : off + ref.length > pages.size
      · rw [if_pos hfit]
        have hne : (listOfByteArray (pages.extract off (off + ref.length))).length != ref.length := by
          rw [length_listOfByteArray, ByteArray.size_extract, Nat.min_def]
          simp only [bne_iff_ne, ne_eq]
          split <;> omega
        simp only [bne_iff_ne, ne_eq] at hne
        rw [if_pos (by simp [hne])]
      · rw [if_neg hfit]
        have heqlen : (listOfByteArray (pages.extract off (off + ref.length))).length
            = ref.length := by
          rw [length_listOfByteArray, ByteArray.size_extract, Nat.min_def]
          split <;> omega
        rw [if_neg (by simp [heqlen])]
        obtain ⟨current, hcur⟩ : ∃ c, c = pages.extract off (off + ref.length) := ⟨_, rfl⟩
        rw [← hcur]
        have hcursize : current.size = ref.length := by
          rw [hcur, ByteArray.size_extract, Nat.min_def]
          split <;> omega
        have hstep := parseEntriesB_eq current (pageEntryCount termCount page) 0 []
        simp only [List.drop_zero] at hstep
        cases hpe : parseEntriesB current (pageEntryCount termCount page) 0 [] with
        | none =>
            rw [hpe] at hstep
            simp only [Option.map_none] at hstep
            rw [← hstep]
            simp
        | some pair =>
            obtain ⟨entries, trailing⟩ := pair
            have htrail : trailing <= current.size :=
              parseEntriesB_le current (pageEntryCount termCount page) 0 [] entries trailing
                (by omega) hpe
            rw [hpe] at hstep
            simp only [Option.map_some] at hstep
            rw [← hstep]
            simp only [someBind]
            by_cases htr : trailing = current.size
            · have hnil : (listOfByteArray current).drop trailing = [] := by
                apply List.drop_eq_nil_of_le
                rw [length_listOfByteArray]; omega
              rw [if_neg (by simp [htr]), hnil]
              simp only [List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, if_false]
              cases entries with
              | nil => rfl
              | cons first others =>
                  dsimp only
                  by_cases hkey : first.key = ref.firstKey
                  · rw [if_neg (by simp [hkey]), if_neg (by simp [hkey])]
                    have hdd : ((listOfByteArray pages).drop off).drop ref.length
                        = (listOfByteArray pages).drop (off + ref.length) := by
                      rw [List.drop_drop]
                    rw [hdd]
                    exact ih pages (off + ref.length) (page + 1) _ (by omega)
                  · rw [if_pos (by simp [hkey]), if_pos (by simp [hkey])]
            · have hlt : trailing < (listOfByteArray current).length := by
                rw [length_listOfByteArray]; omega
              have hne : ((listOfByteArray current).drop trailing).isEmpty = false := by
                rw [List.drop_eq_getElem_cons hlt]; rfl
              rw [if_pos (by simp [htr]), hne]
              simp

/-! ### The whole-artifact decoder -/

theorem drop_take_slice (l : List UInt8) (base pl a n : Nat) (h : a + n ≤ pl) :
    (((l.drop base).take pl).drop a).take n = (l.drop (base + a)).take n := by
  have hpl : a + (pl - a) = pl := by omega
  have h1 : ((l.drop base).drop a).take (pl - a) = ((l.drop base).take pl).drop a := by
    rw [List.take_drop, hpl]
  rw [← h1, List.drop_drop, List.take_take]
  congr 1
  omega

/-- A slice starting at the payload is the byte-array extract of that range. -/
theorem listOfByteArray_slice (bytes : ByteArray) (a n : Nat) :
    listOfByteArray (bytes.extract a (a + n)) = ((listOfByteArray bytes).drop a).take n := by
  rw [listOfByteArray_extract]
  congr 1
  omega

theorem crc32c_payload (bytes : ByteArray) (n : Nat) :
    crc32c (((listOfByteArray bytes).drop 5).take n)
      = crc32cAppendArray 0xFFFFFFFF (bytes.extract 5 (5 + n)) ^^^ 0xFFFFFFFF := by
  rw [← listOfByteArray_slice bytes 5 n, crc32c_listOfByteArray]

theorem directory_slice (bytes : ByteArray) (d p : Nat) :
    ((((listOfByteArray bytes).drop 5).take (32 + 20 + d + p)).drop 52).take d
      = listOfByteArray (bytes.extract 57 (57 + d)) := by
  rw [drop_take_slice (listOfByteArray bytes) 5 (32 + 20 + d + p) 52 d (by omega),
    listOfByteArray_slice]

theorem pages_slice (bytes : ByteArray) (d p : Nat) :
    ((((listOfByteArray bytes).drop 5).take (32 + 20 + d + p)).drop (52 + d)).take p
      = listOfByteArray (bytes.extract (57 + d) (57 + d + p)) := by
  rw [drop_take_slice (listOfByteArray bytes) 5 (32 + 20 + d + p) (52 + d) p (by omega),
    listOfByteArray_slice]
  congr 2
  omega

theorem decodePagesB_zero (termCount : Nat) (refs : List PageRef) (pages : ByteArray)
    (rev : List Entry) :
    decodePagesB termCount refs pages 0 0 rev
      = decodePages termCount refs (listOfByteArray pages) 0 rev := by
  rw [decodePagesB_eq termCount refs pages 0 0 rev (by omega), List.drop_zero]

theorem decode?_eq_spec (bytes : ByteArray) : decode? bytes = decodeSpec? bytes := by
  have hlenB : (listOfByteArray bytes).length = bytes.size := length_listOfByteArray bytes
  simp only [decode?, decodeSpec?, readU32LEB_eq]
  cases hm : readU32LE (listOfByteArray bytes) 0 with
  | none => simp
  | some fm =>
      simp only [someBind]
      by_cases hmagic : fm = magic
      · simp only [if_neg (show ¬((fm != magic) = true) by simp [hmagic])]
        rw [byteAtB_parseU8]
        cases hv : byteAtB bytes 4 with
        | none => simp
        | some fv =>
            simp only [Option.map_some, someBind, hlenB]
            by_cases hver : (fv != version || decide (bytes.size < prefixBytes + crcBytes)) = true
            · simp only [if_pos hver]
            · simp only [if_neg hver]
              have hsize : prefixBytes + crcBytes <= bytes.size := by
                simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hver
                omega
              have h5 : (5 : Nat) <= bytes.size := by
                simp only [prefixBytes, crcBytes] at hsize; omega
              simp only [show (4 : Nat) + 1 = 5 from rfl]
              rw [takeExactB bytes 5 32 h5]
              rw [if_neg (show ¬(5 + 32 > bytes.size) by
                simp only [prefixBytes, crcBytes] at hsize; omega)]
              simp only [someBind, show (5 : Nat) + 32 = 37 from rfl]
              simp only [readU32LE_drop, show (37 : Nat) + 0 = 37 from rfl,
                show (37 : Nat) + 4 = 41 from rfl, show (37 : Nat) + 8 = 45 from rfl,
                show (37 : Nat) + 12 = 49 from rfl, show (37 : Nat) + 16 = 53 from rfl]
              simp only [crc32c_payload, directory_slice, pages_slice]
              simp only [length_listOfByteArray, decodePagesB_zero,
                byteArrayOfList_listOfByteArray]
      · simp only [if_pos (show ((fm != magic) = true) by simp [hmagic])]

/-- The decoder inverts the encoder on the byte object the encoder builds. The
    hypotheses are exactly the guards `supported` and `encode?` check. -/
theorem decodeSpec?_encoded (target : ByteArray) (es : List Entry)
    (htarget : target.size = 32) (hcountfit : es.length < UInt32.size)
    (hok : ∀ e ∈ es, entryOk e) (hinc : strictlyIncreasing es = true)
    (hperm : localIdsPermutation es es.length = true)
    (hpcfit : (pageRefs (pageBytes es) (chunks es.length es)).length < UInt32.size)
    (hdirfit : ((pageRefs (pageBytes es) (chunks es.length es)).flatMap
      encodePageRef).length < UInt32.size)
    (hareafit : (pageBytes es).flatten.length < UInt32.size) :
    decodeSpec? (byteArrayOfList (writeU32LE magic ++ [version] ++
        (target.data.toList ++ writeU32LE (UInt32.ofNat es.length) ++
          writeU32LE (UInt32.ofNat pageTerms) ++
          writeU32LE (UInt32.ofNat (pageRefs (pageBytes es) (chunks es.length es)).length) ++
          writeU32LE (UInt32.ofNat ((pageRefs (pageBytes es)
            (chunks es.length es)).flatMap encodePageRef).length) ++
          writeU32LE (UInt32.ofNat (pageBytes es).flatten.length) ++
          (pageRefs (pageBytes es) (chunks es.length es)).flatMap encodePageRef ++
          (pageBytes es).flatten) ++
        writeU32LE (crc32c (target.data.toList ++ writeU32LE (UInt32.ofNat es.length) ++
          writeU32LE (UInt32.ofNat pageTerms) ++
          writeU32LE (UInt32.ofNat (pageRefs (pageBytes es) (chunks es.length es)).length) ++
          writeU32LE (UInt32.ofNat ((pageRefs (pageBytes es)
            (chunks es.length es)).flatMap encodePageRef).length) ++
          writeU32LE (UInt32.ofNat (pageBytes es).flatten.length) ++
          (pageRefs (pageBytes es) (chunks es.length es)).flatMap encodePageRef ++
          (pageBytes es).flatten))))
      = some { targetIBKSha256 := target, entries := es.toArray } := by
  obtain ⟨EP, hEP⟩ : ∃ EP, EP = chunks es.length es := ⟨_, rfl⟩
  have hPGeq : pageBytes es = EP.map (fun p => p.flatMap encodeEntry) := by
    rw [pageBytes_eq, hEP]
  have hne : ∀ p ∈ EP, p ≠ [] := by rw [hEP]; exact chunks_ne_nil _ _
  have hflatEP : EP.flatten = es := by
    rw [hEP]; exact chunks_flatten es.length es (Nat.le_refl _)
  have hEPlen : EP.length = (es.length + pageTerms - 1) / pageTerms := by
    rw [hEP]; exact chunks_length es.length es (Nat.le_refl _)
  have hReq : pageRefs (pageBytes es) (chunks es.length es) = refsFrom 0 EP := by
    rw [hPGeq, ← hEP]; exact pageRefs_eq EP hne
  rw [hReq, hPGeq]
  obtain ⟨R, hR⟩ : ∃ R, R = refsFrom 0 EP := ⟨_, rfl⟩
  rw [← hR]
  obtain ⟨dir, hdir⟩ : ∃ dir, dir = R.flatMap encodePageRef := ⟨_, rfl⟩
  rw [← hdir]
  obtain ⟨area, harea⟩ : ∃ area, area = (EP.map (fun p => p.flatMap encodeEntry)).flatten :=
    ⟨_, rfl⟩
  rw [← harea]
  rw [hReq, ← hR] at hpcfit
  rw [hReq, ← hR, ← hdir] at hdirfit
  rw [hPGeq, ← harea] at hareafit
  obtain ⟨tl, htlDef⟩ : ∃ tl, tl = target.data.toList := ⟨_, rfl⟩
  rw [← htlDef]
  obtain ⟨pay, hpay⟩ : ∃ pay, pay = tl ++ writeU32LE (UInt32.ofNat es.length) ++
    writeU32LE (UInt32.ofNat pageTerms) ++ writeU32LE (UInt32.ofNat R.length) ++
    writeU32LE (UInt32.ofNat dir.length) ++ writeU32LE (UInt32.ofNat area.length) ++
    dir ++ area := ⟨_, rfl⟩
  rw [← hpay]
  obtain ⟨cb, hcb⟩ : ∃ cb, cb = writeU32LE (crc32c pay) := ⟨_, rfl⟩
  rw [← hcb]
  obtain ⟨inp, hinp⟩ : ∃ inp, inp = writeU32LE magic ++ [version] ++ pay ++ cb := ⟨_, rfl⟩
  rw [← hinp]
  obtain ⟨T, hT⟩ : ∃ T, T = writeU32LE (UInt32.ofNat es.length) ++
    writeU32LE (UInt32.ofNat pageTerms) ++ writeU32LE (UInt32.ofNat R.length) ++
    writeU32LE (UInt32.ofNat dir.length) ++ writeU32LE (UInt32.ofNat area.length) ++
    dir ++ area ++ cb := ⟨_, rfl⟩
  -- derived structure
  have htl : tl.length = 32 := by
    rw [htlDef, Array.length_toList]; exact htarget
  have hRlen : R.length = EP.length := by rw [hR, refsFrom_length]
  have hareaflat : area = EP.flatMap (fun p => p.flatMap encodeEntry) := by
    rw [harea, flatten_map_eq_flatMap]
  have harealen : area.length = (EP.map (fun p => (p.flatMap encodeEntry).length)).sum := by
    rw [harea, List.length_flatten, List.map_map]
    rfl
  have hmemes : ∀ p ∈ EP, ∀ e ∈ p, e ∈ es := by
    intro p hp e he
    rw [← hflatEP]
    exact List.mem_flatten.2 ⟨p, hp, he⟩
  have hokEP : ∀ p ∈ EP, ∀ e ∈ p, entryOk e :=
    fun p hp e he => hok e (hmemes p hp e he)
  have hcount : ∀ (j : Nat) (page : List Entry), EP[j]? = some page →
      pageEntryCount es.length (0 + j) = page.length := by
    intro j page hj
    have hjlt : j < EP.length := (List.getElem?_eq_some_iff.mp hj).1
    rw [hEPlen] at hjlt
    have hgot := chunks_getElem? es.length es j (Nat.le_refl _) hjlt
    rw [← hEP, hj, Option.some.injEq] at hgot
    rw [hgot]
    simp only [pageEntryCount, List.length_take, List.length_drop, Nat.zero_add]
  have hrefbound : ∀ r ∈ R, r.firstKey.length < UInt32.size ∧ r.offset < UInt32.size ∧
      r.length < UInt32.size := by
    intro r hr
    obtain ⟨p, hp, hkey⟩ := refsFrom_mem EP 0 r (hR ▸ hr)
    obtain ⟨e, he, hek⟩ := headKey_mem p (hne p hp)
    have hoff := refsFrom_offset_bound EP 0 r (hR ▸ hr)
    rw [← harealen] at hoff
    refine ⟨?_, by omega, by omega⟩
    rw [hkey, hek]
    exact (hok e (hmemes p hp e he)).2.1
  -- lengths and framings
  have hpaylen : pay.length = 52 + dir.length + area.length := by
    rw [hpay]
    simp only [List.length_append, writeU32LE_length, htl]
  have hcblen : cb.length = 4 := by rw [hcb]; simp
  have hinplen : inp.length = 61 + dir.length + area.length := by
    rw [hinp]
    simp only [List.length_append, writeU32LE_length, List.length_cons, List.length_nil,
      hpaylen, hcblen]
    omega
  have hafterVersion : inp.drop 4 = version :: (pay ++ cb) := by
    rw [hinp,
      show writeU32LE magic ++ [version] ++ pay ++ cb
        = writeU32LE magic ++ (version :: (pay ++ cb)) by
        simp [List.append_assoc]]
    exact List.drop_left' (by simp)
  have hmagic : readU32LE inp 0 = some magic := by
    rw [hinp,
      show writeU32LE magic ++ [version] ++ pay ++ cb
        = writeU32LE magic ++ (version :: (pay ++ cb)) by
        simp [List.append_assoc]]
    exact readU32LE_writeU32LE_append _ _
  have hsplitT : pay ++ cb = tl ++ T := by
    rw [hpay, hT]; simp [List.append_assoc]
  have hfield : ∀ (k : Nat) (pre suf : List UInt8) (val : UInt32),
      T = pre ++ (writeU32LE val ++ suf) → pre.length = k →
      readU32LE T k = some val := by
    intro k pre suf val hsplit hlen
    rw [hsplit, ← hlen]
    exact readU32LE_at_prefix _ _ _
  have h0 := hfield 0 [] (writeU32LE (UInt32.ofNat pageTerms) ++
      writeU32LE (UInt32.ofNat R.length) ++ writeU32LE (UInt32.ofNat dir.length) ++
      writeU32LE (UInt32.ofNat area.length) ++ dir ++ area ++ cb)
    (UInt32.ofNat es.length) (by rw [hT]; simp [List.append_assoc]) rfl
  have h4 := hfield 4 (writeU32LE (UInt32.ofNat es.length))
    (writeU32LE (UInt32.ofNat R.length) ++ writeU32LE (UInt32.ofNat dir.length) ++
      writeU32LE (UInt32.ofNat area.length) ++ dir ++ area ++ cb)
    (UInt32.ofNat pageTerms) (by rw [hT]; simp [List.append_assoc]) (by simp)
  have h8 := hfield 8 (writeU32LE (UInt32.ofNat es.length) ++
      writeU32LE (UInt32.ofNat pageTerms))
    (writeU32LE (UInt32.ofNat dir.length) ++ writeU32LE (UInt32.ofNat area.length) ++
      dir ++ area ++ cb)
    (UInt32.ofNat R.length) (by rw [hT]; simp [List.append_assoc]) (by simp)
  have h12 := hfield 12 (writeU32LE (UInt32.ofNat es.length) ++
      writeU32LE (UInt32.ofNat pageTerms) ++ writeU32LE (UInt32.ofNat R.length))
    (writeU32LE (UInt32.ofNat area.length) ++ dir ++ area ++ cb)
    (UInt32.ofNat dir.length) (by rw [hT]; simp [List.append_assoc]) (by simp)
  have h16 := hfield 16 (writeU32LE (UInt32.ofNat es.length) ++
      writeU32LE (UInt32.ofNat pageTerms) ++ writeU32LE (UInt32.ofNat R.length) ++
      writeU32LE (UInt32.ofNat dir.length))
    (dir ++ area ++ cb)
    (UInt32.ofNat area.length) (by rw [hT]; simp [List.append_assoc]) (by simp)
  have hpaylen' : pay.length = 32 + 20 + dir.length + area.length := by rw [hpaylen]
  have hpayex : (tl ++ T).take (32 + 20 + dir.length + area.length) = pay := by
    rw [← hsplitT]
    exact List.take_left' hpaylen'
  have hcrcread : readU32LE inp (inp.length - crcBytes) = some (crc32c pay) := by
    rw [hinplen, hinp, hcb,
      show writeU32LE magic ++ [version] ++ pay ++ writeU32LE (crc32c pay)
        = (writeU32LE magic ++ [version] ++ pay) ++ (writeU32LE (crc32c pay) ++ []) by
        simp [List.append_assoc],
      show 61 + dir.length + area.length - crcBytes
        = (writeU32LE magic ++ [version] ++ pay).length by
        simp only [List.length_append, writeU32LE_length, List.length_cons,
          List.length_nil, hpaylen, crcBytes]
        omega]
    exact readU32LE_at_prefix _ _ _
  have hdirex : (pay.drop 52).take dir.length = dir := by
    rw [hpay,
      show tl ++ writeU32LE (UInt32.ofNat es.length) ++
          writeU32LE (UInt32.ofNat pageTerms) ++ writeU32LE (UInt32.ofNat R.length) ++
          writeU32LE (UInt32.ofNat dir.length) ++ writeU32LE (UInt32.ofNat area.length) ++
          dir ++ area
        = (tl ++ writeU32LE (UInt32.ofNat es.length) ++
          writeU32LE (UInt32.ofNat pageTerms) ++ writeU32LE (UInt32.ofNat R.length) ++
          writeU32LE (UInt32.ofNat dir.length) ++
          writeU32LE (UInt32.ofNat area.length)) ++ (dir ++ area) by
        simp [List.append_assoc],
      List.drop_left' (by
        simp only [List.length_append, writeU32LE_length, htl])]
    exact List.take_left' rfl
  have hpagex : (pay.drop (52 + dir.length)).take area.length = area := by
    rw [hpay,
      show tl ++ writeU32LE (UInt32.ofNat es.length) ++
          writeU32LE (UInt32.ofNat pageTerms) ++ writeU32LE (UInt32.ofNat R.length) ++
          writeU32LE (UInt32.ofNat dir.length) ++ writeU32LE (UInt32.ofNat area.length) ++
          dir ++ area
        = ((tl ++ writeU32LE (UInt32.ofNat es.length) ++
          writeU32LE (UInt32.ofNat pageTerms) ++ writeU32LE (UInt32.ofNat R.length) ++
          writeU32LE (UInt32.ofNat dir.length) ++
          writeU32LE (UInt32.ofNat area.length)) ++ dir) ++ area by
        simp [List.append_assoc],
      List.drop_left' (by
        simp only [List.length_append, writeU32LE_length, htl])]
    simp
  -- the directory and the pages round trip
  have hdecrefs : parseRefs R.length dir [] = some (R, []) := by
    have hx := parseRefs_ok R [] [] hrefbound
    rw [hdir]
    simpa using hx
  have hcontig : refsContiguous R 0 = true := by
    rw [hR]; exact refsContiguous_refsFrom EP 0 hne
  have hsum : R.foldl (fun total ref => total + ref.length) 0 = area.length := by
    rw [hR, refsFrom_sum, harealen, Nat.zero_add]
  have hdecpages : decodePages es.length R area 0 [] = some es := by
    have hkey := decodePages_ok es.length EP 0 0 [] hne hokEP hcount
    rw [← hR, ← hareaflat] at hkey
    rw [hkey, List.reverse_nil, List.nil_append, hflatEP]
  have hpt : (UInt32.ofNat pageTerms).toNat = pageTerms :=
    u32_toNat_ofNat_of_lt (by simp only [pageTerms]; decide)
  -- assemble
  rw [decodeSpec?, listOfByteArray_byteArrayOfList]
  simp only [hmagic, bind, Option.bind, bne_self_eq_false, Bool.false_eq_true, if_false,
    hafterVersion, parseU8_cons, hsplitT,
    takeExact_append tl T 32 htl,
    h0, h4, h8, h12, h16, u32_toNat_ofNat_of_lt hcountfit, hpt,
    u32_toNat_ofNat_of_lt hpcfit, u32_toNat_ofNat_of_lt hdirfit,
    u32_toNat_ofNat_of_lt hareafit]
  rw [hcrcread, hpayex]
  simp only [bne_self_eq_false, Bool.false_eq_true, if_false, hdirex, hpagex, hdecrefs,
    List.isEmpty_nil, Bool.not_true, hcontig, hsum,
    Bool.or_self, hdecpages, canonicalEntries, hinc, hperm, Bool.and_self, htlDef,
    byteArrayOfList_data_toList]
  rw [if_neg (by
      simp only [Bool.false_or, decide_eq_true_eq, Nat.not_lt, hinplen, prefixBytes, crcBytes]
      omega)]
  rw [if_neg (by
      simp only [Bool.false_or, bne_iff_ne, ne_eq, Decidable.not_not, hRlen, hEPlen])]
  rw [if_neg (by
      simp only [bne_iff_ne, ne_eq, Decidable.not_not, hinplen, crcBytes]
      omega)]

/-- The same statement for the byte-indexed decoder. -/
theorem decode?_encoded (target : ByteArray) (es : List Entry)
    (htarget : target.size = 32) (hcountfit : es.length < UInt32.size)
    (hok : ∀ e ∈ es, entryOk e) (hinc : strictlyIncreasing es = true)
    (hperm : localIdsPermutation es es.length = true)
    (hpcfit : (pageRefs (pageBytes es) (chunks es.length es)).length < UInt32.size)
    (hdirfit : ((pageRefs (pageBytes es) (chunks es.length es)).flatMap
      encodePageRef).length < UInt32.size)
    (hareafit : (pageBytes es).flatten.length < UInt32.size) :
    decode? (byteArrayOfList (writeU32LE magic ++ [version] ++
        (target.data.toList ++ writeU32LE (UInt32.ofNat es.length) ++
          writeU32LE (UInt32.ofNat pageTerms) ++
          writeU32LE (UInt32.ofNat (pageRefs (pageBytes es) (chunks es.length es)).length) ++
          writeU32LE (UInt32.ofNat ((pageRefs (pageBytes es)
            (chunks es.length es)).flatMap encodePageRef).length) ++
          writeU32LE (UInt32.ofNat (pageBytes es).flatten.length) ++
          (pageRefs (pageBytes es) (chunks es.length es)).flatMap encodePageRef ++
          (pageBytes es).flatten) ++
        writeU32LE (crc32c (target.data.toList ++ writeU32LE (UInt32.ofNat es.length) ++
          writeU32LE (UInt32.ofNat pageTerms) ++
          writeU32LE (UInt32.ofNat (pageRefs (pageBytes es) (chunks es.length es)).length) ++
          writeU32LE (UInt32.ofNat ((pageRefs (pageBytes es)
            (chunks es.length es)).flatMap encodePageRef).length) ++
          writeU32LE (UInt32.ofNat (pageBytes es).flatten.length) ++
          (pageRefs (pageBytes es) (chunks es.length es)).flatMap encodePageRef ++
          (pageBytes es).flatten))))
      = some { targetIBKSha256 := target, entries := es.toArray } := by
  rw [decode?_eq_spec]
  exact decodeSpec?_encoded target es htarget hcountfit hok hinc hperm hpcfit hdirfit hareafit

/-- The TLI1 codec round trip: whatever `encode?` accepts, `decode?` returns
unchanged. The only hypothesis is that `encode?` accepted the input.

Every condition the decoder needs is a consequence of `encode?`'s own guards.
`supported` fixes the SHA-256 field at thirty-two bytes, the entry count below
`2^32`, every local ID below the entry count, every key equal to the canonical
term serialization and shorter than `2^32` bytes, and — the three conjuncts
added for this proof — `localIdsPermutation`, which `canonicalEntries`
re-checks, and `termSupported` together with `termFitsU32b`, which
`L4Factoidal.Storage.parseTerm_serializeTerm` needs so `parseEntry` can rebuild
the RDF term. The key ordering is `encode?`'s own second guard, and the three
remaining size conditions are its third. -/
theorem decodeSpec?_encode? (index : Index) (bytes : ByteArray) (h : encode? index = some bytes) :
    decodeSpec? bytes = some index := by
  simp only [encode?] at h
  split at h
  · exact absurd h (by simp)
  · rename_i hsupp
    split at h
    · exact absurd h (by simp)
    · rename_i hordered
      split at h
      · exact absurd h (by simp)
      · rename_i hguard
        injection h with h
        subst h
        have hs : supported index = true := by simpa using hsupp
        simp only [supported, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
          List.all_eq_true] at hs
        obtain ⟨⟨⟨htsize, hcnt⟩, hall⟩, hperm⟩ := hs
        have hlen : index.entries.toList.length = index.entries.size := Array.length_toList
        have hcountfit : index.entries.toList.length < UInt32.size := by
          rw [hlen]; exact hcnt
        have hok : ∀ e ∈ index.entries.toList, entryOk e := by
          intro e he
          obtain ⟨⟨⟨⟨hid, hkey⟩, hklen⟩, hsup⟩, hfit⟩ := hall e he
          exact ⟨hkey, hklen, Nat.lt_trans hid hcnt, hsup, (termFitsU32b_iff e.term).mp hfit⟩
        have hinc : strictlyIncreasing index.entries.toList = true := by
          cases hx : strictlyIncreasing index.entries.toList
          · rw [hx] at hordered; simp at hordered
          · rfl
        have hperm' : localIdsPermutation index.entries.toList
            index.entries.toList.length = true := by rw [hlen]; exact hperm
        simp only [Bool.or_eq_true, Bool.not_eq_true', fitsU32, decide_eq_false_iff_not,
          Nat.not_lt, not_or, Nat.not_le] at hguard
        rw [decodeSpec?_encoded index.targetIBKSha256 index.entries.toList htsize hcountfit
          hok hinc hperm' (by omega) (by omega) (by omega)]

#print axioms parseEntry_encodeEntry
#print axioms parseRefs_ok
#print axioms decodePages_ok
/-- The TLI1 codec round trip for the byte-indexed decoder. -/
theorem decode?_encode? (index : Index) (bytes : ByteArray) (h : encode? index = some bytes) :
    decode? bytes = some index := by
  rw [decode?_eq_spec]
  exact decodeSpec?_encode? index bytes h

#print axioms decodeSpec?_encoded
#print axioms decodeSpec?_encode?
#print axioms decode?_eq_spec
#print axioms decode?_encoded
#print axioms decode?_encode?

end L4Factoidal.Storage.TermLocalIndexWire
