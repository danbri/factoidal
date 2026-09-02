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

`decode?` works on the byte LIST throughout, so the bridge here is only
`listOfByteArray (byteArrayOfList xs) = xs` and its converse. The pagination
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

/-- The decoder inverts the encoder on the byte object the encoder builds. The
    hypotheses are exactly the guards `supported` and `encode?` check. -/
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
  rw [decode?, listOfByteArray_byteArrayOfList]
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
theorem decode?_encode? (index : Index) (bytes : ByteArray) (h : encode? index = some bytes) :
    decode? bytes = some index := by
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
        rw [decode?_encoded index.targetIBKSha256 index.entries.toList htsize hcountfit
          hok hinc hperm' (by omega) (by omega) (by omega)]

#print axioms parseEntry_encodeEntry
#print axioms parseRefs_ok
#print axioms decodePages_ok
#print axioms decode?_encoded
#print axioms decode?_encode?

end L4Factoidal.Storage.TermLocalIndexWire
