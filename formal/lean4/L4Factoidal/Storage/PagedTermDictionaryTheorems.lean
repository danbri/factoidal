/-
L4Factoidal.Storage.PagedTermDictionaryTheorems — PTD1 as the paged
dictionary at the v1 term codec.

    encode? terms = some bytes → decode? bytes = some terms

on the subset `encode?` admits, with no further hypothesis.

The proof is not here. `L4Factoidal.Storage.PagedTermDictionaryCore`
carries the page layout over any `PTD.TermCodec`, and
`PagedTermDictionaryCoreTheorems` carries the round trip over that
abstraction. PTD1 is the instantiation at
`PagedTermDictionary.v1Format`: magic `PTD1`, version byte 1, the
`DeltaLog` term codec over `RDF.Term`. Every definition below is the
generic one at that format — the five that keep their own bodies
(`supported`, `encodePages`, `encode?`, `decodeSpec?`, `decode?`) are
shown equal to the generic ones by `rfl` in the bridge section — so each
theorem here is the generic theorem applied to `v1Format`. PTD2 is the
same layout at term codec v2 and reuses the same proof.

The five theorems whose hypotheses mention the v1 codec's own admission
predicates (`BlockWireV0.termSupported` and `termFitsU32`) convert them
to `PTD.TermCodec.admits` through `termFitsU32b_iff`. That conversion is
`admits_of`, and it is the only proof step left in this module.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.PagedTermDictionary
import L4Factoidal.Storage.PagedTermDictionaryCoreTheorems
import L4Factoidal.Storage.TermCodecTheorems

namespace L4Factoidal.Storage.PagedTermDictionary

open L4Factoidal.RDF
open L4Factoidal.Storage
open L4Factoidal.Storage.BlockWireV0

/-! ## PTD1 is the generic dictionary at the v1 codec

The five definitions that keep their own bodies in
`PagedTermDictionary` are the generic bodies written out; the rest are
already the generic definitions, applied to `v1Format`. -/

theorem supported_eq (terms : Array Term) :
    supported terms = PTD.supported v1Format terms := rfl

theorem encodePages_eq_generic (L : List Term) :
    encodePages L = PTD.encodePages v1Format L := rfl

theorem encode?_eq_generic (terms : Array Term) :
    encode? terms = PTD.encode? v1Format terms := rfl

theorem decodeSpec?_eq_generic (bytes : ByteArray) :
    decodeSpec? bytes = PTD.decodeSpec? v1Format bytes := rfl

theorem decode?_eq_generic (bytes : ByteArray) :
    decode? bytes = PTD.decode? v1Format bytes := rfl

/-- The v1 codec's two admission predicates give the codec-level
admission the generic round trip asks for. -/
theorem admits_of (t : Term) (hsup : termSupported t = true) (hfit : termFitsU32 t) :
    v1Format.codec.admits t = true := by
  show (termSupported t && termFitsU32b t) = true
  rw [Bool.and_eq_true]
  exact ⟨hsup, (termFitsU32b_iff t).mpr hfit⟩

/-! ## Byte array bridge -/

theorem size_byteArrayOfList (xs : List UInt8) :
    (byteArrayOfList xs).size = xs.length := PTD.size_byteArrayOfList xs

theorem listOfByteArray_byteArrayOfList (xs : List UInt8) :
    listOfByteArray (byteArrayOfList xs) = xs := PTD.listOfByteArray_byteArrayOfList xs

theorem extract_byteArrayOfList (xs : List UInt8) (a b : Nat) :
    (byteArrayOfList xs).extract a b = byteArrayOfList ((xs.drop a).take (b - a)) :=
  PTD.extract_byteArrayOfList xs a b

theorem getElem?_byteArrayOfList (xs : List UInt8) (i : Nat) :
    (byteArrayOfList xs)[i]? = xs[i]? := PTD.getElem?_byteArrayOfList xs i

theorem readU32At?_byteArrayOfList (xs : List UInt8) (off : Nat) :
    readU32At? (byteArrayOfList xs) off = readU32LE xs off :=
  PTD.readU32At?_byteArrayOfList xs off

theorem byteArrayOfList_listOfByteArray (bytes : ByteArray) :
    byteArrayOfList (listOfByteArray bytes) = bytes :=
  PTD.byteArrayOfList_listOfByteArray bytes

theorem length_listOfByteArray (bytes : ByteArray) :
    (listOfByteArray bytes).length = bytes.size := PTD.length_listOfByteArray bytes

theorem listOfByteArray_extract (bytes : ByteArray) (a b : Nat) :
    listOfByteArray (bytes.extract a b)
      = ((listOfByteArray bytes).drop a).take (b - a) :=
  PTD.listOfByteArray_extract bytes a b

theorem readU32LE_listOfByteArray (bytes : ByteArray) (off : Nat) :
    readU32LE (listOfByteArray bytes) off = readU32At? bytes off :=
  PTD.readU32LE_listOfByteArray bytes off

theorem crc32c_payload_slice (bytes : ByteArray) :
    crc32c (((listOfByteArray bytes).drop 5).take (bytes.size - 9))
      = crc32cAppendArray 0xFFFFFFFF (bytes.extract 5 (bytes.size - 4)) ^^^ 0xFFFFFFFF :=
  PTD.crc32c_payload_slice bytes

/-! ## Pagination -/

theorem pagesOf_cons (f : Nat) (a : Term) (t : List Term) :
    pagesOf 256 (f + 1) (a :: t)
      = (a :: t).take 256 :: pagesOf 256 f ((a :: t).drop 256) := PTD.pagesOf_cons f a t

theorem pagesOf_flatten : ∀ (f : Nat) (L : List Term), L.length ≤ f →
    (pagesOf 256 f L).flatten = L := PTD.pagesOf_flatten

theorem pagesOf_length : ∀ (f : Nat) (L : List Term), L.length ≤ f →
    (pagesOf 256 f L).length = (L.length + 255) / 256 := PTD.pagesOf_length

theorem pagesOf_getElem? : ∀ (f : Nat) (L : List Term) (j : Nat), L.length ≤ f →
    j < (L.length + 255) / 256 →
    (pagesOf 256 f L)[j]? = some ((L.drop (j * 256)).take 256) := PTD.pagesOf_getElem?

theorem pagesOf_ne_nil : ∀ (f : Nat) (L : List Term) (pg : List Term),
    pg ∈ pagesOf 256 f L → pg ≠ [] := PTD.pagesOf_ne_nil

/-! ## The page directory -/

abbrev dirFrom := PTD.dirFrom

theorem directoryFor_eq (pages : List (List UInt8)) :
    directoryFor pages = dirFrom 0 pages := PTD.directoryFor_eq pages

theorem dirFrom_length (pages : List (List UInt8)) (base : Nat) :
    (dirFrom base pages).length = pages.length := PTD.dirFrom_length pages base

theorem directoryContiguous_dirFrom : ∀ (pages : List (List UInt8)) (base : Nat),
    (∀ page ∈ pages, page ≠ []) → directoryContiguous (dirFrom base pages) base = true :=
  PTD.directoryContiguous_dirFrom

theorem directoryCovers_dirFrom (pages : List (List UInt8))
    (hne : ∀ page ∈ pages, page ≠ []) :
    directoryCovers (dirFrom 0 pages) pages.flatten.length = true :=
  PTD.directoryCovers_dirFrom pages hne

theorem readU32LE_at_prefix (pre : List UInt8) (n : UInt32) (rest : List UInt8) :
    readU32LE (pre ++ (writeU32LE n ++ rest)) pre.length = some n :=
  PTD.readU32LE_at_prefix pre n rest

theorem flatMap_encodeDirectory_length : ∀ (dir : List PageEntry),
    (dir.flatMap encodeDirectory).length = 8 * dir.length :=
  PTD.flatMap_encodeDirectory_length

theorem decodeDirectory?_ok (header : Prefix) (dir : List PageEntry)
    (hpc : header.pageCount = dir.length)
    (hbound : ∀ e ∈ dir, e.offset < UInt32.size ∧ e.length < UInt32.size)
    (hcont : directoryContiguous dir 0 = true) :
    decodeDirectory? header (byteArrayOfList (dir.flatMap encodeDirectory)) = some dir :=
  PTD.decodeDirectory?_ok header dir hpc hbound hcont

/-! ## The fixed prefix -/

theorem decodePrefix_ok (t p c : Nat) (ht : t < UInt32.size) (hp0 : 0 < p)
    (hp : p < UInt32.size) (hc : c < UInt32.size) (hcc : c = (t + p - 1) / p) :
    decodePrefix (byteArrayOfList (writeU32LE magic ++ [version] ++
        writeU32LE (UInt32.ofNat t) ++ writeU32LE (UInt32.ofNat p) ++
        writeU32LE (UInt32.ofNat c)))
      = some { termCount := t, pageTerms := p, pageCount := c } :=
  PTD.decodePrefix_ok v1Format t p c ht hp0 hp hc hcc

/-! ## Pages -/

theorem serializeTerm_ne_nil (t : Term) : serializeTerm t ≠ [] := PTD.encode_ne_nil v1Format t

theorem flatMap_serializeTerm_ne_nil : ∀ (page : List Term), page ≠ [] →
    page.flatMap serializeTerm ≠ [] := PTD.flatMap_encode_ne_nil v1Format

theorem encodePages_eq (L : List Term) :
    encodePages L = (pagesOf 256 L.length L).map (fun page => page.flatMap serializeTerm) :=
  PTD.encodePages_eq v1Format L

theorem foldl_cons_eq : ∀ (page rev : List Term),
    page.foldl (fun acc term => term :: acc) rev = page.reverse ++ rev := PTD.foldl_cons_eq

theorem flatten_map_eq_flatMap {α β : Type} (l : List α) (f : α → List β) :
    (l.map f).flatten = l.flatMap f := PTD.flatten_map_eq_flatMap l f

theorem encodePages_length (L : List Term) :
    (encodePages L).length = (L.length + 255) / 256 := PTD.encodePages_length v1Format L

theorem encodePages_ne_nil (L : List Term) : ∀ page ∈ encodePages L, page ≠ [] :=
  PTD.encodePages_ne_nil v1Format L

theorem decodeTerms_ok (ts : List Term)
    (hsup : ∀ t ∈ ts, termSupported t = true) (hfit : ∀ t ∈ ts, termFitsU32 t) :
    decodeTerms ts.length (ts.flatMap serializeTerm) = some (ts, []) :=
  PTD.decodeTerms_ok v1Format ts (fun t ht => admits_of t (hsup t ht) (hfit t ht))

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
  intro ps i base pre rev hall hbase hsup hfit hcount
  exact PTD.decodePagesGo_ok v1Format header allList ps i base pre rev hall hbase
    (fun page hpage t ht => admits_of t (hsup page hpage t ht) (hfit page hpage t ht))
    hcount

/-! ## Whole-object round trip -/

theorem decodeSpec?_encoded (L : List Term) (sz : Nat)
    (hszL : L.length = sz)
    (hsup : ∀ t ∈ L, termSupported t = true)
    (hfit : ∀ t ∈ L, termFitsU32 t)
    (hn : sz < UInt32.size)
    (hpcfit : (encodePages L).length < UInt32.size)
    (hdirfit : ∀ e ∈ directoryFor (encodePages L),
      e.offset < UInt32.size ∧ e.length < UInt32.size) :
    decodeSpec? (byteArrayOfList
        (writeU32LE magic ++ [version] ++
          (writeU32LE (UInt32.ofNat sz) ++ writeU32LE (UInt32.ofNat defaultPageTerms) ++
            writeU32LE (UInt32.ofNat (encodePages L).length) ++
            (directoryFor (encodePages L)).flatMap encodeDirectory ++
            (encodePages L).flatten) ++
          writeU32LE (crc32c (writeU32LE (UInt32.ofNat sz) ++
            writeU32LE (UInt32.ofNat defaultPageTerms) ++
            writeU32LE (UInt32.ofNat (encodePages L).length) ++
            (directoryFor (encodePages L)).flatMap encodeDirectory ++
            (encodePages L).flatten)))) = some L.toArray :=
  PTD.decodeSpec?_encoded v1Format L sz hszL
    (fun t ht => admits_of t (hsup t ht) (hfit t ht)) hn hpcfit hdirfit

/-- The PTD1 codec round trip for the list specification: whatever
`encode?` accepts, `decodeSpec?` returns unchanged, as the same
`Array Term` in the same order. -/
theorem decodeSpec?_encode? (terms : Array Term)
    (bytes : ByteArray) (h : encode? terms = some bytes) :
    decodeSpec? bytes = some terms := PTD.decodeSpec?_encode? v1Format terms bytes h

/-! ## The admission decoder refines its byte-list specification -/

theorem decode?_eq_spec (bytes : ByteArray) : decode? bytes = decodeSpec? bytes :=
  PTD.decode?_eq_spec v1Format bytes

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
            (encodePages L).flatten)))) = some L.toArray :=
  PTD.decode?_encoded v1Format L sz hszL
    (fun t ht => admits_of t (hsup t ht) (hfit t ht)) hn hpcfit hdirfit

/-- The PTD1 codec round trip: whatever `encode?` accepts, `decode?`
returns unchanged, as the same `Array Term` in the same order. The only
hypothesis is that `encode?` accepted the input. -/
theorem decode?_encode? (terms : Array Term)
    (bytes : ByteArray) (h : encode? terms = some bytes) :
    decode? bytes = some terms := PTD.decode?_encode? v1Format terms bytes h

#print axioms decodePrefix_ok
#print axioms decodeDirectory?_ok
#print axioms decodeTerms_ok
#print axioms decodePagesGo_ok
#print axioms decodeSpec?_encoded
#print axioms decodeSpec?_encode?
#print axioms decode?_eq_spec
#print axioms decode?_encoded
#print axioms decode?_encode?

end L4Factoidal.Storage.PagedTermDictionary
