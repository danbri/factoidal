/-
L4Factoidal.Storage.PagedTermDictionaryTheorems — the round-trip proof for
the PTD1 paged term dictionary codec of
`L4Factoidal.Storage.PagedTermDictionary`.

PTD1 writes a term dictionary as a fixed seventeen-byte prefix, a directory
of eight-byte page entries, and the canonical term bytes of the pages, with
a CRC32C over every post-version byte. `decode?` reads all of that back and
re-checks the page framing before it returns a term array. This module
proves the two agree:

    encode? terms = some bytes → decode? bytes = some terms

on the subset `encode?` admits, together with the term-level admission
conditions of `L4Factoidal.Storage.TermCodecTheorems`.

The proof is layered. The byte-array bridge turns each `ByteArray`
operation the decoder performs into the list operation the encoder built.
The pagination lemmas give `pagesOf` its three properties: it partitions
the term list, its page count is the ceiling division the prefix records,
and its i-th page is `(terms.drop (i * 256)).take 256`. `dirFrom` restates
`directoryFor` as a recursion with a running offset, which is what makes
the directory contiguity and coverage checks provable by induction.
`decodeTermsGo_ok` lifts `parseTerm_serializeTerm` from one term to a whole
page, and `decodePagesGo_ok` lifts that from one page to the page list
under its directory.

`hfit` in the main theorem is not redundant with the `encode?` guards.
`encode?` calls the TOTAL encoder `serializeTerm`, which writes a truncated
u32 length prefix for a string of 2^32 bytes or more; no guard in `encode?`
sees that. The term codec's `termFitsU32` is what excludes it.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.PagedTermDictionary
import L4Factoidal.Storage.TermCodecTheorems

namespace L4Factoidal.Storage.PagedTermDictionary

open L4Factoidal.RDF
open L4Factoidal.Storage
open L4Factoidal.Storage.BlockWireV0

/-! ## Byte array bridge -/

/-- The byte array built from a list has that list's length. -/
theorem size_byteArrayOfList (xs : List UInt8) :
    (byteArrayOfList xs).size = xs.length := by
  simp [byteArrayOfList, ByteArray.size]

/-- Reading a built byte array back gives the list it was built from. -/
theorem listOfByteArray_byteArrayOfList (xs : List UInt8) :
    listOfByteArray (byteArrayOfList xs) = xs := by
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

/-- The decoder's four-byte read is the little-endian list read. -/
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

/-! ## Pagination -/

/-- The recursive step of `pagesOf` on a nonempty term list. -/
theorem pagesOf_cons (f : Nat) (a : Term) (t : List Term) :
    pagesOf 256 (f + 1) (a :: t)
      = (a :: t).take 256 :: pagesOf 256 f ((a :: t).drop 256) := by
  rw [pagesOf]
  simp

/-- With enough fuel the pages partition the term list. -/
theorem pagesOf_flatten : ∀ (f : Nat) (L : List Term), L.length ≤ f →
    (pagesOf 256 f L).flatten = L := by
  intro f
  induction f with
  | zero =>
      intro L hlen
      have hnil : L = [] := List.length_eq_zero_iff.mp (by omega)
      subst hnil; simp [pagesOf]
  | succ f ih =>
      intro L hlen
      match L with
      | [] => simp [pagesOf]
      | a :: t =>
          have hsub : ((a :: t).drop 256).length ≤ f := by
            simp only [List.length_drop, List.length_cons]
            simp only [List.length_cons] at hlen
            omega
          rw [pagesOf_cons, List.flatten_cons, ih ((a :: t).drop 256) hsub]
          exact List.take_append_drop 256 (a :: t)

/-- The page count is the ceiling division the prefix records. -/
theorem pagesOf_length : ∀ (f : Nat) (L : List Term), L.length ≤ f →
    (pagesOf 256 f L).length = (L.length + 255) / 256 := by
  intro f
  induction f with
  | zero =>
      intro L hlen
      have hnil : L = [] := List.length_eq_zero_iff.mp (by omega)
      subst hnil; simp [pagesOf]
  | succ f ih =>
      intro L hlen
      match L with
      | [] => simp [pagesOf]
      | a :: t =>
          have hsub : ((a :: t).drop 256).length ≤ f := by
            simp only [List.length_drop, List.length_cons]
            simp only [List.length_cons] at hlen
            omega
          rw [pagesOf_cons, List.length_cons, ih ((a :: t).drop 256) hsub]
          simp only [List.length_drop, List.length_cons]
          omega

/-- The i-th page is the i-th window of 256 terms. -/
theorem pagesOf_getElem? : ∀ (f : Nat) (L : List Term) (j : Nat), L.length ≤ f →
    j < (L.length + 255) / 256 →
    (pagesOf 256 f L)[j]? = some ((L.drop (j * 256)).take 256) := by
  intro f
  induction f with
  | zero =>
      intro L j hlen hj
      have hnil : L = [] := List.length_eq_zero_iff.mp (by omega)
      subst hnil; simp at hj
  | succ f ih =>
      intro L j hlen hj
      match L with
      | [] => simp at hj
      | a :: t =>
          have hsub : ((a :: t).drop 256).length ≤ f := by
            simp only [List.length_drop, List.length_cons]
            simp only [List.length_cons] at hlen
            omega
          rw [pagesOf_cons]
          match j with
          | 0 => simp
          | k + 1 =>
              have hk : k < (((a :: t).drop 256).length + 255) / 256 := by
                simp only [List.length_drop, List.length_cons]
                simp only [List.length_cons] at hj
                omega
              rw [List.getElem?_cons_succ, ih ((a :: t).drop 256) k hsub hk,
                List.drop_drop]
              congr 3
              omega

/-- No page is empty, which is what makes the directory contiguous. -/
theorem pagesOf_ne_nil : ∀ (f : Nat) (L : List Term) (pg : List Term),
    pg ∈ pagesOf 256 f L → pg ≠ [] := by
  intro f
  induction f with
  | zero => intro L pg hmem; simp [pagesOf] at hmem
  | succ f ih =>
      intro L pg hmem
      match L with
      | [] => simp [pagesOf] at hmem
      | a :: t =>
          rw [pagesOf_cons, List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · simp
          · exact ih _ _ hmem

/-! ## The page directory -/

/-- The directory as a recursion over pages with an explicit running offset. -/
def dirFrom : Nat → List (List UInt8) → List PageEntry
  | _, [] => []
  | base, page :: rest =>
      { offset := base, length := page.length } :: dirFrom (base + page.length) rest

/-- The directory fold accumulates a running offset and reversed entries. -/
theorem directoryFor_fold : ∀ (pages : List (List UInt8)) (base : Nat) (acc : List PageEntry),
    pages.foldl (fun (state : Nat × List PageEntry) page =>
      let (offset, entries) := state
      (offset + page.length, { offset := offset, length := page.length } :: entries)) (base, acc)
      = (base + (pages.map List.length).sum, (dirFrom base pages).reverse ++ acc) := by
  intro pages
  induction pages with
  | nil => intro base acc; simp [dirFrom]
  | cons page rest ih =>
      intro base acc
      rw [List.foldl_cons]
      rw [ih (base + page.length) ({ offset := base, length := page.length } :: acc)]
      simp only [dirFrom, List.map_cons, List.sum_cons, List.reverse_cons,
        List.append_assoc, List.cons_append, List.nil_append]
      rw [Nat.add_assoc]

/-- `directoryFor` is `dirFrom` started at offset zero. -/
theorem directoryFor_eq (pages : List (List UInt8)) :
    directoryFor pages = dirFrom 0 pages := by
  rw [directoryFor]
  simp [directoryFor_fold]

/-- One directory entry per page. -/
theorem dirFrom_length (pages : List (List UInt8)) (base : Nat) :
    (dirFrom base pages).length = pages.length := by
  induction pages generalizing base with
  | nil => simp [dirFrom]
  | cons page rest ih => simp [dirFrom, ih]

/-- A directory of nonempty pages passes the contiguity check. -/
theorem directoryContiguous_dirFrom : ∀ (pages : List (List UInt8)) (base : Nat),
    (∀ page ∈ pages, page ≠ []) → directoryContiguous (dirFrom base pages) base = true := by
  intro pages
  induction pages with
  | nil => intro base _; simp [dirFrom, directoryContiguous]
  | cons page rest ih =>
      intro base hne
      have hp : page ≠ [] := hne page (by simp)
      have hlen : 0 < page.length := List.length_pos_iff.mpr hp
      simp only [dirFrom, directoryContiguous]
      rw [ih (base + page.length) (fun q hq => hne q (by simp [hq]))]
      simp [hlen]

/-- The coverage fold over a contiguous directory sums the page lengths. -/
theorem directoryCovers_fold : ∀ (pages : List (List UInt8)) (base total : Nat),
    (∀ page ∈ pages, page ≠ []) →
    (dirFrom base pages).foldl (fun expected entry =>
        if entry.length > 0 && entry.offset == expected then expected + entry.length
        else total + 1) base
      = base + (pages.map List.length).sum := by
  intro pages
  induction pages with
  | nil => intro base total _; simp [dirFrom]
  | cons page rest ih =>
      intro base total hne
      have hp : page ≠ [] := hne page (by simp)
      have hlen : 0 < page.length := List.length_pos_iff.mpr hp
      simp only [dirFrom, List.foldl_cons, List.map_cons, List.sum_cons]
      rw [if_pos (by simp [hlen])]
      rw [ih (base + page.length) total (fun p hp => hne p (by simp [hp]))]
      omega

/-- A directory of nonempty pages covers exactly the page area. -/
theorem directoryCovers_dirFrom (pages : List (List UInt8))
    (hne : ∀ page ∈ pages, page ≠ []) :
    directoryCovers (dirFrom 0 pages) pages.flatten.length = true := by
  rw [directoryCovers, directoryCovers_fold pages 0 pages.flatten.length hne]
  simp [List.length_flatten]

/-! ## Directory bytes -/

/-- A four-byte field is readable at the length of the framing before it. -/
theorem readU32LE_at_prefix (pre : List UInt8) (n : UInt32) (rest : List UInt8) :
    readU32LE (pre ++ (writeU32LE n ++ rest)) pre.length = some n := by
  rw [← List.append_assoc]
  exact readU32LE_append_writeU32LE pre n rest

/-- The directory decoder inverts `encodeDirectory` entry by entry. -/
theorem decodeDirectoryGo_ok : ∀ (dir : List PageEntry) (pre rest : List UInt8)
    (rev : List PageEntry),
    (∀ e ∈ dir, e.offset < UInt32.size ∧ e.length < UInt32.size) →
    decodeDirectoryGo dir.length
      (byteArrayOfList (pre ++ (dir.flatMap encodeDirectory ++ rest))) pre.length rev
      = some (rev.reverse ++ dir) := by
  intro dir
  induction dir with
  | nil => intro pre rest rev _; simp [decodeDirectoryGo]
  | cons e dir ih =>
      intro pre rest rev hbound
      obtain ⟨hoff, hlen⟩ := hbound e (by simp)
      have hbound' : ∀ x ∈ dir, x.offset < UInt32.size ∧ x.length < UInt32.size :=
        fun x hx => hbound x (by simp [hx])
      have hsplit : pre ++ ((e :: dir).flatMap encodeDirectory ++ rest)
          = pre ++ (writeU32LE (UInt32.ofNat e.offset) ++
              (writeU32LE (UInt32.ofNat e.length) ++ (dir.flatMap encodeDirectory ++ rest))) := by
        simp [encodeDirectory, List.append_assoc]
      have hsplit2 : pre ++ ((e :: dir).flatMap encodeDirectory ++ rest)
          = (pre ++ writeU32LE (UInt32.ofNat e.offset)) ++
              (writeU32LE (UInt32.ofNat e.length) ++ (dir.flatMap encodeDirectory ++ rest)) := by
        rw [hsplit, ← List.append_assoc]
      have hsplit3 : pre ++ ((e :: dir).flatMap encodeDirectory ++ rest)
          = (pre ++ encodeDirectory e) ++ (dir.flatMap encodeDirectory ++ rest) := by
        simp [encodeDirectory, List.append_assoc]
      have hr1 : readU32At? (byteArrayOfList (pre ++ ((e :: dir).flatMap encodeDirectory ++ rest)))
          pre.length = some (UInt32.ofNat e.offset) := by
        rw [readU32At?_byteArrayOfList, hsplit]
        exact readU32LE_at_prefix _ _ _
      have hr2 : readU32At? (byteArrayOfList (pre ++ ((e :: dir).flatMap encodeDirectory ++ rest)))
          (pre.length + 4) = some (UInt32.ofNat e.length) := by
        rw [readU32At?_byteArrayOfList, hsplit2,
          show pre.length + 4 = (pre ++ writeU32LE (UInt32.ofNat e.offset)).length by simp]
        exact readU32LE_at_prefix _ _ _
      have hpre : pre.length + 8 = (pre ++ encodeDirectory e).length := by
        simp [encodeDirectory]
      have hentry : PageEntry.mk (UInt32.ofNat e.offset).toNat
          (UInt32.ofNat e.length).toNat = e := by
        rw [u32_toNat_ofNat_of_lt hoff, u32_toNat_ofNat_of_lt hlen]
      rw [List.length_cons, decodeDirectoryGo]
      simp only [hr1, hr2, bind, Option.bind]
      rw [hentry, hpre, hsplit3,
        ih (pre ++ encodeDirectory e) rest (e :: rev) hbound']
      simp

/-! ## The fixed prefix -/

/-- The seventeen-byte prefix decodes to the header the encoder wrote. -/
theorem decodePrefix_ok (t p c : Nat) (ht : t < UInt32.size) (hp0 : 0 < p)
    (hp : p < UInt32.size) (hc : c < UInt32.size) (hcc : c = (t + p - 1) / p) :
    decodePrefix (byteArrayOfList (writeU32LE magic ++ [version] ++
        writeU32LE (UInt32.ofNat t) ++ writeU32LE (UInt32.ofNat p) ++
        writeU32LE (UInt32.ofNat c)))
      = some { termCount := t, pageTerms := p, pageCount := c } := by
  have hsize : (byteArrayOfList (writeU32LE magic ++ [version] ++
      writeU32LE (UInt32.ofNat t) ++ writeU32LE (UInt32.ofNat p) ++
      writeU32LE (UInt32.ofNat c))).size = prefixBytes := by
    rw [size_byteArrayOfList]
    simp [writeU32LE, prefixBytes]
  have hm : readU32At? (byteArrayOfList (writeU32LE magic ++ [version] ++
      writeU32LE (UInt32.ofNat t) ++ writeU32LE (UInt32.ofNat p) ++
      writeU32LE (UInt32.ofNat c))) 0 = some magic := by
    rw [readU32At?_byteArrayOfList,
      show writeU32LE magic ++ [version] ++ writeU32LE (UInt32.ofNat t) ++
          writeU32LE (UInt32.ofNat p) ++ writeU32LE (UInt32.ofNat c)
        = writeU32LE magic ++ ([version] ++ writeU32LE (UInt32.ofNat t) ++
          writeU32LE (UInt32.ofNat p) ++ writeU32LE (UInt32.ofNat c)) by
        simp [List.append_assoc]]
    exact readU32LE_writeU32LE_append _ _
  have hv : (byteArrayOfList (writeU32LE magic ++ [version] ++
      writeU32LE (UInt32.ofNat t) ++ writeU32LE (UInt32.ofNat p) ++
      writeU32LE (UInt32.ofNat c)))[4]? = some version := by
    rw [getElem?_byteArrayOfList]
    simp [writeU32LE]
  have ht5 : readU32At? (byteArrayOfList (writeU32LE magic ++ [version] ++
      writeU32LE (UInt32.ofNat t) ++ writeU32LE (UInt32.ofNat p) ++
      writeU32LE (UInt32.ofNat c))) 5 = some (UInt32.ofNat t) := by
    rw [readU32At?_byteArrayOfList,
      show writeU32LE magic ++ [version] ++ writeU32LE (UInt32.ofNat t) ++
          writeU32LE (UInt32.ofNat p) ++ writeU32LE (UInt32.ofNat c)
        = (writeU32LE magic ++ [version]) ++ (writeU32LE (UInt32.ofNat t) ++
          (writeU32LE (UInt32.ofNat p) ++ writeU32LE (UInt32.ofNat c))) by
        simp [List.append_assoc],
      show (5 : Nat) = (writeU32LE magic ++ [version]).length by simp]
    exact readU32LE_at_prefix _ _ _
  have hp9 : readU32At? (byteArrayOfList (writeU32LE magic ++ [version] ++
      writeU32LE (UInt32.ofNat t) ++ writeU32LE (UInt32.ofNat p) ++
      writeU32LE (UInt32.ofNat c))) 9 = some (UInt32.ofNat p) := by
    rw [readU32At?_byteArrayOfList,
      show writeU32LE magic ++ [version] ++ writeU32LE (UInt32.ofNat t) ++
          writeU32LE (UInt32.ofNat p) ++ writeU32LE (UInt32.ofNat c)
        = (writeU32LE magic ++ [version] ++ writeU32LE (UInt32.ofNat t)) ++
          (writeU32LE (UInt32.ofNat p) ++ writeU32LE (UInt32.ofNat c)) by
        simp [List.append_assoc],
      show (9 : Nat)
        = (writeU32LE magic ++ [version] ++ writeU32LE (UInt32.ofNat t)).length by simp]
    exact readU32LE_at_prefix _ _ _
  have hc13 : readU32At? (byteArrayOfList (writeU32LE magic ++ [version] ++
      writeU32LE (UInt32.ofNat t) ++ writeU32LE (UInt32.ofNat p) ++
      writeU32LE (UInt32.ofNat c))) 13 = some (UInt32.ofNat c) := by
    rw [readU32At?_byteArrayOfList,
      show writeU32LE magic ++ [version] ++ writeU32LE (UInt32.ofNat t) ++
          writeU32LE (UInt32.ofNat p) ++ writeU32LE (UInt32.ofNat c)
        = (writeU32LE magic ++ [version] ++ writeU32LE (UInt32.ofNat t) ++
          writeU32LE (UInt32.ofNat p)) ++ (writeU32LE (UInt32.ofNat c) ++ []) by
        simp [List.append_assoc],
      show (13 : Nat) = (writeU32LE magic ++ [version] ++ writeU32LE (UInt32.ofNat t) ++
        writeU32LE (UInt32.ofNat p)).length by simp]
    exact readU32LE_at_prefix _ _ _
  rw [decodePrefix]
  simp only [hsize, hm, hv, ht5, hp9, hc13, bind, Option.bind, bne_self_eq_false,
    Bool.false_eq_true, if_false, u32_toNat_ofNat_of_lt ht, u32_toNat_ofNat_of_lt hp,
    u32_toNat_ofNat_of_lt hc]
  rw [if_neg (by simp; omega), if_neg (by simp [hcc])]

/-! ## The directory object -/

/-- Each directory entry occupies eight bytes. -/
theorem flatMap_encodeDirectory_length : ∀ (dir : List PageEntry),
    (dir.flatMap encodeDirectory).length = 8 * dir.length := by
  intro dir
  induction dir with
  | nil => simp
  | cons e rest ih => simp [encodeDirectory, ih]; omega

/-- The whole directory object round trips. -/
theorem decodeDirectory?_ok (header : Prefix) (dir : List PageEntry)
    (hpc : header.pageCount = dir.length)
    (hbound : ∀ e ∈ dir, e.offset < UInt32.size ∧ e.length < UInt32.size)
    (hcont : directoryContiguous dir 0 = true) :
    decodeDirectory? header (byteArrayOfList (dir.flatMap encodeDirectory)) = some dir := by
  have hgo : decodeDirectoryGo dir.length
      (byteArrayOfList (dir.flatMap encodeDirectory)) 0 [] = some dir := by
    have hx := decodeDirectoryGo_ok dir [] [] [] hbound
    simpa using hx
  have hsize : (byteArrayOfList (dir.flatMap encodeDirectory)).size = header.pageCount * 8 := by
    rw [size_byteArrayOfList, flatMap_encodeDirectory_length, hpc]
    omega
  rw [decodeDirectory?]
  simp only [hsize, bne_self_eq_false, Bool.false_eq_true, if_false, hpc, hgo,
    bind, Option.bind, hcont, Bool.not_true, if_false]

/-! ## Nonempty pages -/

/-- Every serialised term starts with a tag byte. -/
theorem serializeTerm_ne_nil (t : Term) : serializeTerm t ≠ [] := by
  cases t <;> simp [serializeTerm]

/-- A nonempty page has nonempty page bytes. -/
theorem flatMap_serializeTerm_ne_nil : ∀ (page : List Term), page ≠ [] →
    page.flatMap serializeTerm ≠ [] := by
  intro page hne
  match page with
  | [] => exact absurd rfl hne
  | t :: rest =>
      simp only [List.flatMap_cons, ne_eq, List.append_eq_nil_iff, not_and]
      intro hcon
      exact absurd hcon (serializeTerm_ne_nil t)

/-- `encodePages` is `pagesOf` at the default page size, term-encoded. -/
theorem encodePages_eq (L : List Term) :
    encodePages L = (pagesOf 256 L.length L).map (fun page => page.flatMap serializeTerm) := rfl

/-! ## Page contents -/

/-- The decoder's reverse accumulator prepends the page in reverse. -/
theorem foldl_cons_eq : ∀ (page rev : List Term),
    page.foldl (fun acc term => term :: acc) rev = page.reverse ++ rev := by
  intro page
  induction page with
  | nil => intro rev; simp
  | cons a t ih => intro rev; simp [ih]

/-- A run of serialised terms decodes back, leaving the trailing bytes. -/
theorem decodeTermsGo_ok : ∀ (ts : List Term) (rest : List UInt8) (rev : List Term),
    (∀ t ∈ ts, termSupported t = true) → (∀ t ∈ ts, termFitsU32 t) →
    decodeTermsGo ts.length (ts.flatMap serializeTerm ++ rest) rev
      = some (rev.reverse ++ ts, rest) := by
  intro ts
  induction ts with
  | nil => intro rest rev _ _; simp [decodeTermsGo]
  | cons t ts ih =>
      intro rest rev hsup hfit
      have hsplit : (t :: ts).flatMap serializeTerm ++ rest
          = serializeTerm t ++ (ts.flatMap serializeTerm ++ rest) := by
        simp [List.append_assoc]
      rw [List.length_cons, decodeTermsGo, hsplit,
        parseTerm_serializeTerm t (ts.flatMap serializeTerm ++ rest)
          (hsup t (by simp)) (hfit t (by simp))]
      simp only [bind, Option.bind]
      rw [ih rest (t :: rev) (fun x hx => hsup x (by simp [hx]))
        (fun x hx => hfit x (by simp [hx]))]
      simp

/-- One page of serialised terms decodes back with no trailing bytes. -/
theorem decodeTerms_ok (ts : List Term)
    (hsup : ∀ t ∈ ts, termSupported t = true) (hfit : ∀ t ∈ ts, termFitsU32 t) :
    decodeTerms ts.length (ts.flatMap serializeTerm) = some (ts, []) := by
  rw [decodeTerms,
    show ts.flatMap serializeTerm = ts.flatMap serializeTerm ++ [] by simp,
    decodeTermsGo_ok ts [] [] hsup hfit]
  simp

/-- The page walk decodes every declared page and ends at the last byte. -/
theorem decodePagesGo_ok (header : Prefix) (allList : List UInt8) :
    ∀ (ps : List (List Term)) (i base : Nat) (pre : List UInt8) (rev : List Term),
      allList = pre ++ ps.flatMap (fun page => page.flatMap serializeTerm) →
      pre.length = base →
      (∀ page ∈ ps, ∀ t ∈ page, termSupported t = true) →
      (∀ page ∈ ps, ∀ t ∈ page, termFitsU32 t) →
      (∀ j page, ps[j]? = some page → pageTermCount header (i + j) = page.length) →
      decodePagesGo header i
          (dirFrom base (ps.map (fun page => page.flatMap serializeTerm)))
          (byteArrayOfList allList) base rev
        = some (rev.reverse ++ ps.flatten) := by
  intro ps
  induction ps with
  | nil =>
      intro i base pre rev hall hbase _ _ _
      simp only [List.map_nil, dirFrom, decodePagesGo]
      have hsize : (byteArrayOfList allList).size = base := by
        rw [size_byteArrayOfList, hall, ← hbase]
        simp
      rw [hsize]
      simp
  | cons page ps ih =>
      intro i base pre rev hall hbase hsup hfit hcount
      have hcount0 : pageTermCount header i = page.length := by
        have := hcount 0 page (by simp)
        simpa using this
      have hall' : allList = pre ++ (page.flatMap serializeTerm ++
          ps.flatMap (fun p => p.flatMap serializeTerm)) := by
        rw [hall]; simp
      have hdrop : allList.drop base = page.flatMap serializeTerm ++
          ps.flatMap (fun p => p.flatMap serializeTerm) := by
        rw [hall', ← hbase, List.drop_left]
      have hcur : (byteArrayOfList allList).extract base
          (base + (page.flatMap serializeTerm).length)
          = byteArrayOfList (page.flatMap serializeTerm) := by
        rw [extract_byteArrayOfList]
        congr 1
        rw [hdrop]
        simp
      simp only [List.map_cons, dirFrom, decodePagesGo]
      rw [hcur]
      simp only [size_byteArrayOfList, bne_self_eq_false, Bool.false_eq_true, if_false,
        listOfByteArray_byteArrayOfList, hcount0]
      rw [decodeTerms_ok page (hsup page (by simp)) (hfit page (by simp))]
      simp only [bind, Option.bind, List.isEmpty_nil, Bool.not_true,
        Bool.false_eq_true, if_false, foldl_cons_eq]
      rw [ih (i + 1) (base + (page.flatMap serializeTerm).length)
        (pre ++ page.flatMap serializeTerm) (page.reverse ++ rev)
        (by rw [hall']; simp [List.append_assoc])
        (by rw [← hbase]; simp)
        (fun p hp => hsup p (by simp [hp]))
        (fun p hp => hfit p (by simp [hp]))
        (fun j p hj => by
          have := hcount (j + 1) p (by simpa using hj)
          rw [← this]
          congr 1
          omega)]
      simp


/-! ## Whole-object round trip -/

/-- Flattening a map is the corresponding `flatMap`. -/
theorem flatten_map_eq_flatMap {α β : Type} (l : List α) (f : α → List β) :
    (l.map f).flatten = l.flatMap f := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih]

/-- The encoded page count is the ceiling division of the term count. -/
theorem encodePages_length (L : List Term) :
    (encodePages L).length = (L.length + 255) / 256 := by
  rw [encodePages_eq, List.length_map, pagesOf_length L.length L (Nat.le_refl _)]

/-- No encoded page is empty. -/
theorem encodePages_ne_nil (L : List Term) : ∀ page ∈ encodePages L, page ≠ [] := by
  rw [encodePages_eq]
  intro page hmem
  rw [List.mem_map] at hmem
  obtain ⟨pg, hpg, hpe⟩ := hmem
  rw [← hpe]
  exact flatMap_serializeTerm_ne_nil pg (pagesOf_ne_nil L.length L pg hpg)

/-- The decoder inverts the encoder on the byte object the encoder builds.
The three size hypotheses are exactly the guards `encode?` checks. -/
theorem decode?_encoded (L : List Term) (sz : Nat)
    (hszL : L.length = sz)
    (hsup : ∀ t ∈ L, termSupported t = true)
    (hfit : ∀ t ∈ L, termFitsU32 t)
    (hn : sz < UInt32.size)
    (hpcfit : (encodePages L).length < UInt32.size)
    (hdirfit : ∀ e ∈ directoryFor (encodePages L),
      e.offset < UInt32.size ∧ e.length < UInt32.size) :
    decode? (byteArrayOfList
        (writeU32LE magic ++ [version] ++
          (writeU32LE (UInt32.ofNat sz) ++ writeU32LE (UInt32.ofNat defaultPageTerms) ++
            writeU32LE (UInt32.ofNat (encodePages L).length) ++
            (directoryFor (encodePages L)).flatMap encodeDirectory ++
            (encodePages L).flatten) ++
          writeU32LE (crc32c (writeU32LE (UInt32.ofNat sz) ++
            writeU32LE (UInt32.ofNat defaultPageTerms) ++
            writeU32LE (UInt32.ofNat (encodePages L).length) ++
            (directoryFor (encodePages L)).flatMap encodeDirectory ++
            (encodePages L).flatten)))) = some L.toArray := by
  obtain ⟨P, hP⟩ : ∃ P, P = encodePages L := ⟨_, rfl⟩
  rw [← hP] at hpcfit hdirfit ⊢
  obtain ⟨D, hD⟩ : ∃ D, D = directoryFor P := ⟨_, rfl⟩
  rw [← hD] at hdirfit ⊢
  obtain ⟨pay, hpay⟩ : ∃ pay, pay = writeU32LE (UInt32.ofNat sz) ++
      writeU32LE (UInt32.ofNat defaultPageTerms) ++ writeU32LE (UInt32.ofNat P.length) ++
      D.flatMap encodeDirectory ++ P.flatten := ⟨_, rfl⟩
  rw [← hpay]
  obtain ⟨inp, hinp⟩ : ∃ inp, inp = writeU32LE magic ++ [version] ++ pay ++
      writeU32LE (crc32c pay) := ⟨_, rfl⟩
  rw [← hinp]
  obtain ⟨pre17, hpre17⟩ : ∃ q, q = writeU32LE magic ++ [version] ++
      writeU32LE (UInt32.ofNat sz) ++ writeU32LE (UInt32.ofNat defaultPageTerms) ++
      writeU32LE (UInt32.ofNat P.length) := ⟨_, rfl⟩
  -- structural facts about the page list and its directory
  have hPlen : P.length = (L.length + 255) / 256 := by rw [hP, encodePages_length]
  have hPne : ∀ page ∈ P, page ≠ [] := by rw [hP]; exact encodePages_ne_nil L
  have hDeq : D = dirFrom 0 P := by rw [hD, directoryFor_eq]
  have hDlen : D.length = P.length := by rw [hDeq, dirFrom_length]
  have hdirlen : (D.flatMap encodeDirectory).length = 8 * P.length := by
    rw [flatMap_encodeDirectory_length, hDlen]
  have hcont : directoryContiguous D 0 = true := by
    rw [hDeq]; exact directoryContiguous_dirFrom P 0 hPne
  have hcov : directoryCovers D P.flatten.length = true := by
    rw [hDeq]; exact directoryCovers_dirFrom P hPne
  have hpre17len : pre17.length = 17 := by rw [hpre17]; simp
  have hpaylen : pay.length = 12 + 8 * P.length + P.flatten.length := by
    rw [hpay]
    simp only [List.length_append, writeU32LE_length, hdirlen]
  have hinplen : inp.length = 21 + 8 * P.length + P.flatten.length := by
    rw [hinp]
    simp only [List.length_append, writeU32LE_length, List.length_cons, List.length_nil, hpaylen]
    omega
  -- four framings of the same byte list
  have hsplitA : inp = pre17 ++ (D.flatMap encodeDirectory ++
      (P.flatten ++ writeU32LE (crc32c pay))) := by
    rw [hinp, hpre17, hpay]; simp [List.append_assoc]
  have hsplitB : inp = (pre17 ++ D.flatMap encodeDirectory) ++
      (P.flatten ++ writeU32LE (crc32c pay)) := by
    rw [hsplitA, List.append_assoc]
  have hsplitC : inp = (writeU32LE magic ++ [version]) ++ (pay ++ writeU32LE (crc32c pay)) := by
    rw [hinp]; simp [List.append_assoc]
  have hsplitD : inp = (writeU32LE magic ++ [version] ++ pay) ++
      (writeU32LE (crc32c pay) ++ []) := by
    rw [hinp]; simp [List.append_assoc]
  -- the fixed prefix decodes to the header the encoder wrote
  have hex0 : (byteArrayOfList inp).extract 0 prefixBytes = byteArrayOfList pre17 := by
    rw [extract_byteArrayOfList]
    congr 1
    rw [List.drop_zero, hsplitA]
    exact List.take_left' (by simp only [hpre17len, prefixBytes])
  have hprefix : decodePrefix ((byteArrayOfList inp).extract 0 prefixBytes)
      = some { termCount := sz, pageTerms := defaultPageTerms, pageCount := P.length } := by
    rw [hex0, hpre17]
    exact decodePrefix_ok sz defaultPageTerms P.length hn (by decide) (by decide) hpcfit
      (by rw [hPlen, hszL]; simp only [defaultPageTerms]; omega)
  -- the payload the decoder hashes is the payload the encoder hashed
  have hpayex : (inp.drop 5).take (inp.length - 9) = pay := by
    rw [hinplen, hsplitC, List.drop_left' (by simp)]
    exact List.take_left' (by rw [hpaylen]; omega)
  have hcrcread : readU32LE inp (inp.length - 4) = some (crc32c pay) := by
    rw [hinplen, hsplitD,
      show 21 + 8 * P.length + P.flatten.length - 4
        = (writeU32LE magic ++ [version] ++ pay).length by
        simp only [List.length_append, writeU32LE_length, List.length_cons,
          List.length_nil, hpaylen]; omega]
    exact readU32LE_at_prefix _ _ _
  -- the directory and page areas are the byte ranges the encoder laid out
  have hdirex : (byteArrayOfList inp).extract prefixBytes (prefixBytes + P.length * 8)
      = byteArrayOfList (D.flatMap encodeDirectory) := by
    rw [extract_byteArrayOfList]
    congr 1
    rw [hsplitA, List.drop_left' (by simp only [hpre17len, prefixBytes])]
    exact List.take_left' (by rw [hdirlen]; simp only [prefixBytes]; omega)
  have hpagex : (byteArrayOfList inp).extract (prefixBytes + P.length * 8)
      ((byteArrayOfList inp).size - 4) = byteArrayOfList P.flatten := by
    rw [extract_byteArrayOfList, size_byteArrayOfList, hinplen]
    congr 1
    rw [hsplitB, List.drop_left'
      (by simp only [List.length_append, hpre17len, hdirlen, prefixBytes]; omega)]
    exact List.take_left' (by simp only [prefixBytes]; omega)
  -- the directory round trips
  have hdecdir : decodeDirectory?
      { termCount := sz, pageTerms := defaultPageTerms, pageCount := P.length }
      (byteArrayOfList (D.flatMap encodeDirectory)) = some D :=
    decodeDirectory?_ok _ D hDlen.symm hdirfit hcont
  -- the pages round trip
  have hpagesdec : decodePages?
      { termCount := sz, pageTerms := defaultPageTerms, pageCount := P.length } 0 D
      (byteArrayOfList P.flatten) = some L := by
    have hPmap : P = (pagesOf 256 L.length L).map (fun page => page.flatMap serializeTerm) := by
      rw [hP, encodePages_eq]
    have hflat : P.flatten = [] ++ (pagesOf 256 L.length L).flatMap
        (fun page => page.flatMap serializeTerm) := by
      rw [hPmap, flatten_map_eq_flatMap, List.nil_append]
    have hpgflat : (pagesOf 256 L.length L).flatten = L := pagesOf_flatten L.length L (Nat.le_refl _)
    have hsupp : ∀ page ∈ pagesOf 256 L.length L, ∀ t ∈ page, termSupported t = true := by
      intro page hpage t ht
      exact hsup t (by rw [← hpgflat]; exact List.mem_flatten.2 ⟨page, hpage, ht⟩)
    have hfitp : ∀ page ∈ pagesOf 256 L.length L, ∀ t ∈ page, termFitsU32 t := by
      intro page hpage t ht
      exact hfit t (by rw [← hpgflat]; exact List.mem_flatten.2 ⟨page, hpage, ht⟩)
    have hcountp : ∀ (j : Nat) (page : List Term), (pagesOf 256 L.length L)[j]? = some page →
        pageTermCount { termCount := sz, pageTerms := defaultPageTerms, pageCount := P.length }
          (0 + j) = page.length := by
      intro j page hj
      have hjlt : j < (pagesOf 256 L.length L).length :=
        (List.getElem?_eq_some_iff.mp hj).1
      rw [pagesOf_length L.length L (Nat.le_refl _)] at hjlt
      have hgot := pagesOf_getElem? L.length L j (Nat.le_refl _) hjlt
      rw [hj, Option.some.injEq] at hgot
      rw [hgot]
      simp only [pageTermCount, List.length_take, List.length_drop, defaultPageTerms,
        Nat.zero_add, hszL]
    have key := decodePagesGo_ok
      { termCount := sz, pageTerms := defaultPageTerms, pageCount := P.length }
      P.flatten (pagesOf 256 L.length L) 0 0 [] [] hflat rfl hsupp hfitp hcountp
    rw [← hPmap] at key
    rw [decodePages?, hDeq, key, List.reverse_nil, List.nil_append, hpgflat]
  -- assemble
  simp only [decode?, listOfByteArray_byteArrayOfList, hprefix, bind, Option.bind]
  rw [if_neg (by rw [hinplen]; simp only [prefixBytes]; omega)]
  rw [hpayex, hcrcread]
  simp only [bne_self_eq_false, Bool.false_eq_true, if_false]
  rw [hdirex, hdecdir]
  simp only [pageAreaOffset]
  simp only [hpagex]
  simp only [size_byteArrayOfList, hcov, Bool.not_true, Bool.false_eq_true, if_false]
  rw [hpagesdec]
  simp only [hszL, bne_self_eq_false, Bool.false_eq_true, if_false]


/-- The PTD1 codec round trip: whatever `encode?` accepts, `decode?` returns
unchanged, as the same `Array Term` in the same order.

`hsup` and `hfit` are the admission conditions of the term codec beneath this
one (`L4Factoidal.Storage.parseTerm_serializeTerm`): `termSupported` excludes
RDF 1.2 triple terms and literals carrying a base direction, and `termFitsU32`
says every length-prefixed string in the term is shorter than the u32 length
field. `encode?` itself gates on `termSupported` through `supported`, but it
calls the TOTAL encoder `serializeTerm`, which would write a truncated length
prefix for an oversized string; `hfit` is what excludes that. The remaining
size conditions the decoder needs — the term count, the page count and every
directory offset and length below `UInt32.size` — are the guards `encode?`
already checks, so they are read out of `h` rather than assumed. -/
theorem decode?_encode? (terms : Array Term)
    (hsup : ∀ t ∈ terms.toList, BlockWireV0.termSupported t = true)
    (hfit : ∀ t ∈ terms.toList, termFitsU32 t)
    (bytes : ByteArray) (h : encode? terms = some bytes) :
    decode? bytes = some terms := by
  simp only [encode?] at h
  split at h
  · exact absurd h (by simp)
  · rename_i hsupp
    split at h
    · exact absurd h (by simp)
    · rename_i hguard
      injection h with h
      subst h
      simp [supported, fitsU32] at hsupp hguard
      obtain ⟨-, hszfit⟩ := hsupp
      obtain ⟨⟨hpcfit, -⟩, hdirall⟩ := hguard
      have hu32 : (4294967296 : Nat) = UInt32.size := rfl
      rw [decode?_encoded terms.toList terms.size Array.length_toList hsup hfit
        (hu32 ▸ hszfit) (hu32 ▸ hpcfit)
        (fun e he => ⟨hu32 ▸ (hdirall e he).1, hu32 ▸ (hdirall e he).2⟩)]

#print axioms decodePrefix_ok
#print axioms decodeDirectory?_ok
#print axioms decodeTerms_ok
#print axioms decodePagesGo_ok
#print axioms decode?_encoded
#print axioms decode?_encode?

end L4Factoidal.Storage.PagedTermDictionary
