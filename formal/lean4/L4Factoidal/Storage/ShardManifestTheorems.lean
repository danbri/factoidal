/-
L4Factoidal.Storage.ShardManifestTheorems — the round-trip proof for the
Shardborough manifest codec of `L4Factoidal.Storage.ShardManifest`.

The statement is the one the IBK4 block theorems use, with the same single
hypothesis:

    encode? manifest = some bytes → decode? bytes = some manifest

It is stated over EVERY manifest wire version, SBM0 through SBM7, because
`encode?` and `decode?` are one pair of functions with a version field. A
version-restricted statement would leave the older versions carrying the
byte-format claim of the `#guard` fixtures alone.

The layering is the one the sidecar codecs use: a byte-array bridge, the
fixed-width u32 field, the length-prefixed UTF-8 string, then one lemma per
framed object — the graph name, the graph-set summary, the entry, the entry
list — and the assembly. Every admission test `decode?` performs is discharged
from `encode?`'s own `valid` and `encodable` gates; there is no hypothesis
beyond `encode? manifest = some bytes`.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.ShardManifest

namespace L4Factoidal.Storage.ShardManifest

open L4Factoidal.RDF

/-! ## The byte-array bridge

`encode?` assembles a `List UInt8` and wraps it; `decode?` unwraps and reads a
`List UInt8`. Digests and Merkle roots travel the other way: the encoder writes
`ByteArray.toList` and the decoder rebuilds with `byteArrayOfList`. -/

theorem listOfByteArray_byteArrayOfList (xs : List UInt8) :
    listOfByteArray (byteArrayOfList xs) = xs := by
  simp [listOfByteArray, byteArrayOfList]

/-- `ByteArray.toList` is the element list of the underlying array. Lean core
    defines it by an index loop, so this is proved by the loop's own
    invariant. -/
private theorem byteArray_toList_loop (bs : ByteArray) (i : Nat) (r : List UInt8) :
    ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
  have key : ∀ n i r, bs.size - i = n →
      ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
    intro n
    induction n with
    | zero =>
        intro i r h
        rw [ByteArray.toList.loop]
        have hi : ¬ (i < bs.size) := by omega
        simp only [hi, if_false]
        have hle : bs.data.toList.length ≤ i := by
          rw [Array.length_toList]; exact Nat.le_of_not_lt hi
        rw [List.drop_eq_nil_of_le hle]
        simp
    | succ n ih =>
        intro i r h
        rw [ByteArray.toList.loop]
        have hi : i < bs.size := by omega
        simp only [hi, if_true]
        rw [ih (i + 1) (bs.get! i :: r) (by omega)]
        have hlen : i < bs.data.toList.length := by
          rw [Array.length_toList]; exact hi
        rw [List.drop_eq_getElem_cons hlen]
        have hg : bs.get! i = bs.data.toList[i] := by
          rw [Array.getElem_toList]
          show bs.data[i]! = bs.data[i]
          rw [getElem!_pos]
        rw [hg]
        simp
  exact key (bs.size - i) i r rfl

theorem byteArray_toList_eq (bs : ByteArray) : bs.toList = bs.data.toList := by
  rw [ByteArray.toList, byteArray_toList_loop]; simp

theorem byteArrayOfList_toList (bs : ByteArray) : byteArrayOfList bs.toList = bs := by
  rw [byteArray_toList_eq, byteArrayOfList]

theorem length_toList (bs : ByteArray) : bs.toList.length = bs.size := by
  rw [byteArray_toList_eq, Array.length_toList]; rfl

/-! ## Boolean conjunction chains

`&&` is left-associative, so the nth conjunct of an admission gate is reached
by a chain of `andL` closed by one `andR`. -/

private theorem andL {a b : Bool} (h : (a && b) = true) : a = true :=
  ((Bool.and_eq_true _ _).mp h).1

private theorem andR {a b : Bool} (h : (a && b) = true) : b = true :=
  ((Bool.and_eq_true _ _).mp h).2

/-! ## Fixed-width and length-prefixed fields -/

/-- The exact-length reader consumes a known prefix and leaves the tail. -/
theorem takeExact_append (xs rest : List UInt8) :
    takeExact xs.length (xs ++ rest) = some (xs, rest) := by
  rw [takeExact]
  simp

/-- A `Nat` field below the u32 limit survives the round trip through the
    little-endian wire representation. -/
theorem readU32LE_ofNat_append (n : Nat) (h : fitsU32 n) (rest : List UInt8) :
    (readU32LE (writeU32LE (UInt32.ofNat n) ++ rest) 0).map UInt32.toNat = some n := by
  rw [readU32LE_writeU32LE_append]
  have hlt : n < UInt32.size := by
    have h' : n < 4294967296 := by simpa [fitsU32] using h
    have hsize : UInt32.size = 4294967296 := rfl
    omega
  simp [u32_toNat_ofNat_of_lt hlt]

/-- The length-prefixed UTF-8 decoder inverts its encoder and returns the
    trailing bytes unchanged. -/
theorem decodeString_encodeString (s : String) (rest : List UInt8)
    (h : fitsU32 s.toUTF8.size) :
    decodeString (encodeString s ++ rest) = some (s, rest) := by
  have hlen : s.toUTF8.toList.length < UInt32.size := by
    rw [length_toList]
    have h' : s.toUTF8.size < 4294967296 := by simpa [fitsU32] using h
    have hsize : UInt32.size = 4294967296 := rfl
    omega
  rw [encodeString, decodeString]
  simp only [List.append_assoc, readU32LE_writeU32LE_append]
  simp only [bind, Option.bind, u32_toNat_ofNat_of_lt hlen]
  have hdrop : (writeU32LE (UInt32.ofNat s.toUTF8.toList.length) ++
      (s.toUTF8.toList ++ rest)).drop 4 = s.toUTF8.toList ++ rest := by
    simp [writeU32LE]
  rw [hdrop]
  simp only [List.take_left, List.drop_left, bne_self_eq_false, Bool.false_eq_true, if_false]
  have hba : (⟨s.toUTF8.toList.toArray⟩ : ByteArray) = s.toUTF8 := by
    rw [byteArray_toList_eq]
  have hfrom : String.fromUTF8? ⟨s.toUTF8.toList.toArray⟩ = some s := by
    rw [hba]
    simp [String.fromUTF8?, s.isValidUTF8, String.fromUTF8]
  rw [hfrom]

/-- A fixed four-byte field is exactly what a reader steps over. -/
theorem drop4_writeU32LE (n : UInt32) (t : List UInt8) : (writeU32LE n ++ t).drop 4 = t := by
  simp [writeU32LE]

/-- Reading a field at offset four is reading the next field of the tail. -/
theorem readU32LE_drop4 (n : UInt32) (t : List UInt8) :
    readU32LE (writeU32LE n ++ t) 4 = readU32LE t 0 := by
  simp [readU32LE, writeU32LE]

theorem takeExact_of_length (xs rest : List UInt8) (n : Nat) (h : xs.length = n) :
    takeExact n (xs ++ rest) = some (xs, rest) := by
  subst h; exact takeExact_append xs rest

/-- The single-byte reader consumes exactly the head byte. -/
theorem parseU8_cons (b : UInt8) (rest : List UInt8) : parseU8 (b :: rest) = some (b, rest) := rfl

/-! ## The common entry fields -/

theorem decodeCommon_encodeCommon (entry : Entry) (rest : List UInt8)
    (hpred : fitsU32 entry.predicate.val.toUTF8.size)
    (hkey : fitsU32 entry.artifact.key.value.toUTF8.size)
    (hbytes : fitsU32 entry.artifact.bytes)
    (hdigest : entry.artifact.sha256.size = 32)
    (hrows : fitsU32 entry.rows) (hord : fitsU32 entry.ordinal) :
    decodeCommon (encodeCommon entry ++ rest) =
      some ({ predicateText := entry.predicate.val, keyText := entry.artifact.key.value,
              artifactBytes := entry.artifact.bytes, digest := entry.artifact.sha256.toList,
              rows := entry.rows, ordinal := entry.ordinal }, rest) := by
  have hsize : UInt32.size = 4294967296 := rfl
  have hb : entry.artifact.bytes < UInt32.size := by
    have := (by simpa [fitsU32] using hbytes : entry.artifact.bytes < 4294967296); omega
  have hr : entry.rows < UInt32.size := by
    have := (by simpa [fitsU32] using hrows : entry.rows < 4294967296); omega
  have ho : entry.ordinal < UInt32.size := by
    have := (by simpa [fitsU32] using hord : entry.ordinal < 4294967296); omega
  have h32 : entry.artifact.sha256.toList.length = 32 := by rw [length_toList]; exact hdigest
  rw [encodeCommon, decodeCommon]
  simp only [List.append_assoc]
  rw [decodeString_encodeString _ _ hpred]
  simp only [bind, Option.bind]
  rw [decodeString_encodeString _ _ hkey]
  simp only [readU32LE_writeU32LE_append, drop4_writeU32LE]
  rw [← h32, takeExact_append]
  simp only [readU32LE_writeU32LE_append, readU32LE_drop4, u32_toNat_ofNat_of_lt hb,
    u32_toNat_ofNat_of_lt hr, u32_toNat_ofNat_of_lt ho]
  rw [← List.append_assoc, takeExact_of_length _ _ _ (by simp)]

/-! ## The Merkle chunk commitment -/

theorem drop8_two_fields (n m : UInt32) (t : List UInt8) :
    (writeU32LE n ++ (writeU32LE m ++ t)).drop 8 = t := by
  simp [writeU32LE]

theorem decodeChunkedRef_encodeChunkedRef (chunked : ChunkedArtifact.Ref) (totalBytes : Nat)
    (rest : List UInt8) (hcb : fitsU32 chunked.chunkBytes) (hcc : fitsU32 chunked.chunkCount)
    (hroot : chunked.root.size = 32) (htotal : chunked.totalBytes = totalBytes) :
    decodeChunkedRef totalBytes (encodeChunkedRef chunked ++ rest) = some (chunked, rest) := by
  have hsize : UInt32.size = 4294967296 := rfl
  have hb : chunked.chunkBytes < UInt32.size := by
    have := (by simpa [fitsU32] using hcb : chunked.chunkBytes < 4294967296); omega
  have hc : chunked.chunkCount < UInt32.size := by
    have := (by simpa [fitsU32] using hcc : chunked.chunkCount < 4294967296); omega
  have h32 : chunked.root.toList.length = 32 := by rw [length_toList]; exact hroot
  rw [encodeChunkedRef, decodeChunkedRef]
  simp only [List.append_assoc, bind, Option.bind, readU32LE_writeU32LE_append,
    readU32LE_drop4, drop8_two_fields]
  rw [← h32, takeExact_append]
  simp only [u32_toNat_ofNat_of_lt hb, u32_toNat_ofNat_of_lt hc, byteArrayOfList_toList,
    Option.some.injEq, Prod.mk.injEq, and_true]
  rw [← htotal]

/-! ## Index sidecar references -/

theorem decodeSidecarRef_encodeSidecarRef (index : ArtifactRef) (chunked : ChunkedArtifact.Ref)
    (rest : List UInt8) (hchunked : index.chunked = some chunked)
    (hkey : fitsU32 index.key.value.toUTF8.size) (hbytes : fitsU32 index.bytes)
    (hsha : index.sha256.size = 32) (hcb : fitsU32 chunked.chunkBytes)
    (hcc : fitsU32 chunked.chunkCount) (hroot : chunked.root.size = 32)
    (htotal : chunked.totalBytes = index.bytes) :
    decodeSidecarRef (encodeSidecarRef index ++ rest) = some (index, rest) := by
  have hsize : UInt32.size = 4294967296 := rfl
  have hb : index.bytes < UInt32.size := by
    have := (by simpa [fitsU32] using hbytes : index.bytes < 4294967296); omega
  have h32 : index.sha256.toList.length = 32 := by rw [length_toList]; exact hsha
  rw [encodeSidecarRef, hchunked, decodeSidecarRef]
  simp only [List.append_assoc]
  rw [decodeString_encodeString _ _ hkey]
  simp only [bind, Option.bind, readU32LE_writeU32LE_append, drop4_writeU32LE]
  rw [← h32, takeExact_append]
  simp only [u32_toNat_ofNat_of_lt hb]
  rw [decodeChunkedRef_encodeChunkedRef chunked index.bytes _ hcb hcc hroot htotal]
  simp only [byteArrayOfList_toList, Option.some.injEq, Prod.mk.injEq, and_true]
  rw [← hchunked]

/-! ## Graph names and the graph-set summary -/

theorem decodeGraphName_encodeGraphName (name : GraphName) (rest : List UInt8)
    (henc : graphNameEncodable name) (hadm : graphNameAdmitted name) :
    decodeGraphName (encodeGraphName name ++ rest) = some (name, rest) := by
  have htext : decodeString (encodeString (graphNameText name) ++ rest) =
      some (graphNameText name, rest) :=
    decodeString_encodeString _ _ (by simpa [graphNameEncodable] using henc)
  cases name with
  | defaultGraph =>
      rw [show graphNameText GraphName.defaultGraph = "" from rfl] at htext
      simp only [encodeGraphName, decodeGraphName, graphNameTag, graphNameText,
        List.singleton_append, List.cons_append, List.nil_append,
        parseU8_cons, bind, Option.bind]
      rw [htext]
      simp
  | iri value =>
      rw [show graphNameText (GraphName.iri value) = value.val from rfl] at htext
      simp only [encodeGraphName, decodeGraphName, graphNameTag, graphNameText,
        List.singleton_append, List.cons_append, List.nil_append,
        parseU8_cons, bind, Option.bind]
      rw [htext]
      simp only [show ((1 : UInt8) == 0) = false from rfl,
        show ((1 : UInt8) == 1) = true from rfl, if_false, if_true]
      rw [dif_pos value.property]
      simp
  | bnode label =>
      have hne : label.isEmpty = false := by simpa [graphNameAdmitted] using hadm
      rw [show graphNameText (GraphName.bnode label) = label from rfl] at htext
      simp only [encodeGraphName, decodeGraphName, graphNameTag, graphNameText,
        List.singleton_append, List.cons_append, List.nil_append,
        parseU8_cons, bind, Option.bind]
      rw [htext]
      simp [hne]

theorem decodeGraphNames_flatMap : ∀ (names : List GraphName) (rest : List UInt8),
    names.all graphNameEncodable → names.all graphNameAdmitted →
    decodeGraphNames names.length (names.flatMap encodeGraphName ++ rest) = some (names, rest) := by
  intro names
  induction names with
  | nil => intro rest _ _; simp [decodeGraphNames]
  | cons name tail ih =>
      intro rest henc hadm
      simp only [List.all_cons, Bool.and_eq_true] at henc hadm
      simp only [List.length_cons, List.flatMap_cons, List.append_assoc, decodeGraphNames]
      rw [decodeGraphName_encodeGraphName name _ henc.1 hadm.1]
      simp only [bind, Option.bind]
      rw [ih rest henc.2 hadm.2]

/-! ## The SBM7 quad tail -/

theorem decodeQuadTail_encodeQuadTail (kind : BlockLayout) (scope : String)
    (names : List GraphName) (rest : List UInt8)
    (hscope : fitsU32 scope.toUTF8.size) (hcount : fitsU32 names.length)
    (henc : names.all graphNameEncodable) (hadm : names.all graphNameAdmitted) :
    decodeQuadTail (encodeQuadTail kind scope names ++ rest) = some ((kind, scope, names), rest) := by
  have hsize : UInt32.size = 4294967296 := rfl
  have hn : names.length < UInt32.size := by
    have := (by simpa [fitsU32] using hcount : names.length < 4294967296); omega
  rw [encodeQuadTail, decodeQuadTail]
  simp only [List.singleton_append, List.cons_append, List.append_assoc, List.nil_append,
    parseU8_cons, bind, Option.bind]
  have hkind : blockLayoutOfTag (blockLayoutTag kind) = some kind := by
    cases kind <;> rfl
  rw [hkind]
  simp only [bind, Option.bind, List.append_assoc]
  rw [decodeString_encodeString _ _ hscope]
  simp only [bind, Option.bind, readU32LE_writeU32LE_append, u32_toNat_ofNat_of_lt hn]
  rw [takeExact_of_length (writeU32LE (UInt32.ofNat names.length)) _ 4 (by simp)]
  simp only [bind, Option.bind]
  rw [decodeGraphNames_flatMap names rest henc hadm]

/-! ## One manifest entry

The conditions `decodeEntry` re-checks are exactly the conjuncts of `valid`
and `encodable` that `encode?` already ran, so the entry lemma takes them as
`entryValid` and `encodableEntry` and nothing else. -/

/-- The fields every version writes are bounded in every version. -/
theorem encodableEntry_common (version : Nat) (entry : Entry)
    (he : encodableEntry version entry) :
    fitsU32 entry.predicate.val.toUTF8.size ∧ fitsU32 entry.artifact.key.value.toUTF8.size ∧
      fitsU32 entry.artifact.bytes ∧ fitsU32 entry.rows ∧ fitsU32 entry.ordinal ∧
      entry.artifact.sha256.size = 32 := by
  have hc : encodableCommon entry = true := andL (andL (andL (andL (andL he))))
  simp only [encodableCommon, Bool.and_eq_true, beq_iff_eq] at hc
  exact ⟨hc.1.1.1.1.1, hc.1.1.1.1.2, hc.1.1.1.2, hc.1.1.2, hc.1.2, hc.2⟩

/-- The reconstruction step: the record `decodeEntry` builds from decoded
    fields is the entry that produced them. -/
theorem entry_rebuild (entry : Entry) (chunked : Option ChunkedArtifact.Ref)
    (subjectIndex termIndex objectIndex : Option ArtifactRef)
    (blockLayout : Option BlockLayout) (scope : String) (names : List GraphName)
    (hc : entry.artifact.chunked = chunked) (hs : entry.subjectIndex = subjectIndex)
    (ht : entry.termIndex = termIndex) (ho : entry.objectIndex = objectIndex)
    (hl : entry.blockLayout = blockLayout) (hsc : entry.blankNodeScope = scope)
    (hg : entry.graphSet = names) (h : isIri entry.predicate.val) :
    ({ predicate := ⟨entry.predicate.val, h⟩
       artifact := { key := { value := entry.artifact.key.value }, bytes := entry.artifact.bytes,
                     sha256 := byteArrayOfList entry.artifact.sha256.toList, chunked := chunked }
       subjectIndex := subjectIndex
       termIndex := termIndex
       objectIndex := objectIndex
       blockLayout := blockLayout
       blankNodeScope := scope
       graphSet := names
       rows := entry.rows
       ordinal := entry.ordinal } : Entry) = entry := by
  rw [byteArrayOfList_toList, ← hc, ← hs, ← ht, ← ho, ← hl, ← hsc, ← hg]

/-! ### Reading the two admission gates

`entryValid` and `encodableEntry` are left-associated Boolean conjunctions, so
each conjunct is reached by a chain of `andL`/`andR`. The version-dependent
conjuncts are `match` expressions; with a literal version and a known option
shape they reduce, so `exact` on the reduced form suffices. -/

/-- One index sidecar round-trips under the manifest's own two gates. -/
theorem sidecar_roundTrip (version : Nat)
    (hversion : version = 3 ∨ version = 4 ∨ version = 5 ∨ version = 6)
    (index : ArtifactRef) (rest : List UInt8)
    (hav : artifactValidFor version index) (hen : encodableSidecar index) :
    decodeSidecarRef (encodeSidecarRef index ++ rest) = some (index, rest) := by
  obtain ⟨c, hc⟩ : ∃ c, index.chunked = some c := by
    cases h : index.chunked with
    | some c => exact ⟨c, rfl⟩
    | none => have hm := andR hen; rw [h] at hm; simp at hm
  have hkey : fitsU32 index.key.value.toUTF8.size := andL (andL (andL hen))
  have hbytes : fitsU32 index.bytes := andR (andL (andL hen))
  have hsha : index.sha256.size = 32 := by simpa using andR (andL hen)
  have hmc : encodableChunked c := by have h := andR hen; rw [hc] at h; exact h
  have htotal : c.totalBytes = index.bytes := by
    have h := andR hav
    rw [hc] at h
    rcases hversion with rfl | rfl | rfl | rfl <;> simpa using andR h
  exact decodeSidecarRef_encodeSidecarRef index c rest hc hkey hbytes hsha
    (andL (andL hmc)) (andR (andL hmc)) (by simpa using andR hmc) htotal

/-- The primary artifact's chunk commitment round-trips under the same two
    gates. -/
theorem chunked_roundTrip (version : Nat)
    (hversion : version = 1 ∨ version = 2 ∨ version = 3 ∨ version = 4 ∨ version = 5 ∨
      version = 6 ∨ version = 7)
    (entry : Entry) (c : ChunkedArtifact.Ref) (rest : List UInt8)
    (hc : entry.artifact.chunked = some c)
    (hav : artifactValidFor version entry.artifact) (hen : encodableChunked c) :
    decodeChunkedRef entry.artifact.bytes (encodeChunkedRef c ++ rest) = some (c, rest) := by
  have htotal : c.totalBytes = entry.artifact.bytes := by
    have h := andR hav
    rw [hc] at h
    rcases hversion with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simpa using andR h
  exact decodeChunkedRef_encodeChunkedRef c entry.artifact.bytes rest
    (andL (andL hen)) (andR (andL hen)) (by simpa using andR hen) htotal

/-! ### The entry round trip, one wire-version shape at a time

Five shapes cover the eight versions: no commitment (SBM0), a chunk commitment
(SBM1/SBM2), plus a subject sidecar (SBM3), plus a term sidecar (SBM4/SBM5),
plus an object sidecar (SBM6), and the chunk commitment plus the quad tail with
no sidecar (SBM7). -/

theorem decodeEntry_encodeEntry_v0 (entry : Entry) (rest : List UInt8)
    (hv : entryValid 0 entry) (he : encodableEntry 0 entry) :
    decodeEntry 0 (encodeEntry 0 entry ++ rest) = some (entry, rest) := by
  obtain ⟨hp, hk, hb, hr, hord, hd⟩ := encodableEntry_common 0 entry he
  have hav : artifactValidFor 0 entry.artifact := andR (andL (andL (andL (andL (andL hv)))))
  have hchunk : entry.artifact.chunked = none := by
    cases h : entry.artifact.chunked with
    | none => rfl
    | some c => have hm := andR hav; rw [h] at hm; simp at hm
  have hs : entry.subjectIndex = none := by
    cases h : entry.subjectIndex with
    | none => rfl
    | some i => have hm := andR (andL (andL (andL (andL hv)))); rw [h] at hm; simp at hm
  have ht : entry.termIndex = none := by
    cases h : entry.termIndex with
    | none => rfl
    | some i => have hm := andR (andL (andL (andL hv))); rw [h] at hm; simp at hm
  have hoi : entry.objectIndex = none := by
    cases h : entry.objectIndex with
    | none => rfl
    | some i => have hm := andR (andL (andL hv)); rw [h] at hm; simp at hm
  have hl : entry.blockLayout = none := by
    cases h : entry.blockLayout with
    | none => rfl
    | some k => have hm := andR (andL hv); rw [h] at hm; simp at hm
  have hsc : entry.blankNodeScope = "" := by simpa using andL (andR hv)
  have hg : entry.graphSet = [] := by simpa using andR (andR hv)
  simp only [encodeEntry, hchunk, decodeEntry, List.append_assoc]
  rw [decodeCommon_encodeCommon entry _ hp hk hb hd hr hord]
  simp only [bind, Option.bind]
  rw [dif_pos entry.predicate.property]
  simp only [Option.some.injEq, Prod.mk.injEq, and_true]
  exact entry_rebuild entry none none none none none "" [] hchunk hs ht hoi hl hsc hg
    entry.predicate.property

theorem decodeEntry_encodeEntry_chunkedOnly (version : Nat)
    (hversion : version = 1 ∨ version = 2) (entry : Entry) (rest : List UInt8)
    (hv : entryValid version entry) (he : encodableEntry version entry) :
    decodeEntry version (encodeEntry version entry ++ rest) = some (entry, rest) := by
  rcases hversion with rfl | rfl
  all_goals (
    obtain ⟨hp, hk, hb, hr, hord, hd⟩ := encodableEntry_common _ entry he
    have hav : artifactValidFor _ entry.artifact := andR (andL (andL (andL (andL (andL hv)))))
    obtain ⟨c, hchunk⟩ : ∃ c, entry.artifact.chunked = some c := by
      cases h : entry.artifact.chunked with
      | some c => exact ⟨c, rfl⟩
      | none => have hm := andR hav; rw [h] at hm; simp at hm
    have hs : entry.subjectIndex = none := by
      cases h : entry.subjectIndex with
      | none => rfl
      | some i => have hm := andR (andL (andL (andL (andL hv)))); rw [h] at hm; simp at hm
    have ht : entry.termIndex = none := by
      cases h : entry.termIndex with
      | none => rfl
      | some i => have hm := andR (andL (andL (andL hv))); rw [h] at hm; simp at hm
    have hoi : entry.objectIndex = none := by
      cases h : entry.objectIndex with
      | none => rfl
      | some i => have hm := andR (andL (andL hv)); rw [h] at hm; simp at hm
    have hl : entry.blockLayout = none := by
      cases h : entry.blockLayout with
      | none => rfl
      | some k => have hm := andR (andL hv); rw [h] at hm; simp at hm
    have hsc : entry.blankNodeScope = "" := by simpa using andL (andR hv)
    have hg : entry.graphSet = [] := by simpa using andR (andR hv)
    have hMc : encodableChunked c := by
      have hm := andR (andL (andL (andL (andL he)))); rw [hchunk] at hm; exact hm
    simp only [encodeEntry, hchunk, decodeEntry, List.append_assoc]
    rw [decodeCommon_encodeCommon entry _ hp hk hb hd hr hord]
    simp only [bind, Option.bind]
    rw [dif_pos entry.predicate.property,
      chunked_roundTrip _ (by decide) entry c _ hchunk hav hMc]
    simp only [bind, Option.bind, Option.some.injEq, Prod.mk.injEq, and_true]
    exact entry_rebuild entry (some c) none none none none "" [] hchunk hs ht hoi hl hsc hg
      entry.predicate.property)

theorem decodeEntry_encodeEntry_subject (entry : Entry) (rest : List UInt8)
    (hv : entryValid 3 entry) (he : encodableEntry 3 entry) :
    decodeEntry 3 (encodeEntry 3 entry ++ rest) = some (entry, rest) := by
  obtain ⟨hp, hk, hb, hr, hord, hd⟩ := encodableEntry_common 3 entry he
  have hav : artifactValidFor 3 entry.artifact := andR (andL (andL (andL (andL (andL hv)))))
  obtain ⟨c, hchunk⟩ : ∃ c, entry.artifact.chunked = some c := by
    cases h : entry.artifact.chunked with
    | some c => exact ⟨c, rfl⟩
    | none => have hm := andR hav; rw [h] at hm; simp at hm
  obtain ⟨i, hsi⟩ : ∃ i, entry.subjectIndex = some i := by
    cases h : entry.subjectIndex with
    | some i => exact ⟨i, rfl⟩
    | none => have hm := andR (andL (andL (andL (andL hv)))); rw [h] at hm; simp at hm
  have ht : entry.termIndex = none := by
    cases h : entry.termIndex with
    | none => rfl
    | some x => have hm := andR (andL (andL (andL hv))); rw [h] at hm; simp at hm
  have hoi : entry.objectIndex = none := by
    cases h : entry.objectIndex with
    | none => rfl
    | some x => have hm := andR (andL (andL hv)); rw [h] at hm; simp at hm
  have hl : entry.blockLayout = none := by
    cases h : entry.blockLayout with
    | none => rfl
    | some k => have hm := andR (andL hv); rw [h] at hm; simp at hm
  have hsc : entry.blankNodeScope = "" := by simpa using andL (andR hv)
  have hg : entry.graphSet = [] := by simpa using andR (andR hv)
  have hMc : encodableChunked c := by
    have hm := andR (andL (andL (andL (andL he)))); rw [hchunk] at hm; exact hm
  have hSav : artifactValidFor 3 i := by
    have hm := andR (andL (andL (andL (andL hv)))); rw [hsi] at hm; exact andL hm
  have hMs : encodableSidecar i := by
    have hm := andR (andL (andL (andL he))); rw [hsi] at hm; exact hm
  simp only [encodeEntry, hchunk, hsi, ht, hoi, decodeEntry, List.append_assoc]
  rw [decodeCommon_encodeCommon entry _ hp hk hb hd hr hord]
  simp only [bind, Option.bind]
  rw [dif_pos entry.predicate.property,
    chunked_roundTrip _ (by decide) entry c _ hchunk hav hMc]
  simp only [bind, Option.bind]
  rw [sidecar_roundTrip _ (by decide) i _ hSav hMs]
  simp only [bind, Option.bind, Option.some.injEq, Prod.mk.injEq, and_true]
  exact entry_rebuild entry (some c) (some i) none none none "" [] hchunk hsi ht hoi hl hsc hg
    entry.predicate.property

theorem decodeEntry_encodeEntry_subjectTerm (version : Nat)
    (hversion : version = 4 ∨ version = 5) (entry : Entry) (rest : List UInt8)
    (hv : entryValid version entry) (he : encodableEntry version entry) :
    decodeEntry version (encodeEntry version entry ++ rest) = some (entry, rest) := by
  rcases hversion with rfl | rfl
  all_goals (
    obtain ⟨hp, hk, hb, hr, hord, hd⟩ := encodableEntry_common _ entry he
    have hav : artifactValidFor _ entry.artifact := andR (andL (andL (andL (andL (andL hv)))))
    obtain ⟨c, hchunk⟩ : ∃ c, entry.artifact.chunked = some c := by
      cases h : entry.artifact.chunked with
      | some c => exact ⟨c, rfl⟩
      | none => have hm := andR hav; rw [h] at hm; simp at hm
    obtain ⟨i, hsi⟩ : ∃ i, entry.subjectIndex = some i := by
      cases h : entry.subjectIndex with
      | some i => exact ⟨i, rfl⟩
      | none => have hm := andR (andL (andL (andL (andL hv)))); rw [h] at hm; simp at hm
    obtain ⟨t, hti⟩ : ∃ t, entry.termIndex = some t := by
      cases h : entry.termIndex with
      | some t => exact ⟨t, rfl⟩
      | none => have hm := andR (andL (andL (andL hv))); rw [h] at hm; simp at hm
    have hoi : entry.objectIndex = none := by
      cases h : entry.objectIndex with
      | none => rfl
      | some x => have hm := andR (andL (andL hv)); rw [h] at hm; simp at hm
    have hl : entry.blockLayout = none := by
      cases h : entry.blockLayout with
      | none => rfl
      | some k => have hm := andR (andL hv); rw [h] at hm; simp at hm
    have hsc : entry.blankNodeScope = "" := by simpa using andL (andR hv)
    have hg : entry.graphSet = [] := by simpa using andR (andR hv)
    have hMc : encodableChunked c := by
      have hm := andR (andL (andL (andL (andL he)))); rw [hchunk] at hm; exact hm
    have hms := andR (andL (andL (andL (andL hv))))
    rw [hsi] at hms
    have hSav := andL hms
    have hMs : encodableSidecar i := by
      have hm := andR (andL (andL (andL he))); rw [hsi] at hm; exact hm
    have hmt := andR (andL (andL (andL hv)))
    rw [hti] at hmt
    have hTav := andL hmt
    have hMt : encodableSidecar t := by
      have hm := andR (andL (andL he)); rw [hti] at hm; exact hm
    simp only [encodeEntry, hchunk, hsi, hti, hoi, decodeEntry, List.append_assoc]
    rw [decodeCommon_encodeCommon entry _ hp hk hb hd hr hord]
    simp only [bind, Option.bind]
    rw [dif_pos entry.predicate.property,
      chunked_roundTrip _ (by decide) entry c _ hchunk hav hMc]
    simp only [bind, Option.bind]
    rw [sidecar_roundTrip _ (by decide) i _ hSav hMs]
    simp only [bind, Option.bind]
    rw [sidecar_roundTrip _ (by decide) t _ hTav hMt]
    simp only [bind, Option.bind, Option.some.injEq, Prod.mk.injEq, and_true]
    exact entry_rebuild entry (some c) (some i) (some t) none none "" [] hchunk hsi hti hoi hl
      hsc hg entry.predicate.property)

theorem decodeEntry_encodeEntry_object (entry : Entry) (rest : List UInt8)
    (hv : entryValid 6 entry) (he : encodableEntry 6 entry) :
    decodeEntry 6 (encodeEntry 6 entry ++ rest) = some (entry, rest) := by
  obtain ⟨hp, hk, hb, hr, hord, hd⟩ := encodableEntry_common 6 entry he
  have hav : artifactValidFor 6 entry.artifact := andR (andL (andL (andL (andL (andL hv)))))
  obtain ⟨c, hchunk⟩ : ∃ c, entry.artifact.chunked = some c := by
    cases h : entry.artifact.chunked with
    | some c => exact ⟨c, rfl⟩
    | none => have hm := andR hav; rw [h] at hm; simp at hm
  obtain ⟨i, hsi⟩ : ∃ i, entry.subjectIndex = some i := by
    cases h : entry.subjectIndex with
    | some i => exact ⟨i, rfl⟩
    | none => have hm := andR (andL (andL (andL (andL hv)))); rw [h] at hm; simp at hm
  obtain ⟨t, hti⟩ : ∃ t, entry.termIndex = some t := by
    cases h : entry.termIndex with
    | some t => exact ⟨t, rfl⟩
    | none => have hm := andR (andL (andL (andL hv))); rw [h] at hm; simp at hm
  obtain ⟨o, hoi⟩ : ∃ o, entry.objectIndex = some o := by
    cases h : entry.objectIndex with
    | some o => exact ⟨o, rfl⟩
    | none => have hm := andR (andL (andL hv)); rw [h] at hm; simp at hm
  have hl : entry.blockLayout = none := by
    cases h : entry.blockLayout with
    | none => rfl
    | some k => have hm := andR (andL hv); rw [h] at hm; simp at hm
  have hsc : entry.blankNodeScope = "" := by simpa using andL (andR hv)
  have hg : entry.graphSet = [] := by simpa using andR (andR hv)
  have hMc : encodableChunked c := by
    have hm := andR (andL (andL (andL (andL he)))); rw [hchunk] at hm; exact hm
  have hSav : artifactValidFor 6 i := by
    have hm := andR (andL (andL (andL (andL hv)))); rw [hsi] at hm; exact andL hm
  have hMs : encodableSidecar i := by
    have hm := andR (andL (andL (andL he))); rw [hsi] at hm; exact hm
  have hTav : artifactValidFor 6 t := by
    have hm := andR (andL (andL (andL hv))); rw [hti] at hm; exact andL hm
  have hMt : encodableSidecar t := by
    have hm := andR (andL (andL he)); rw [hti] at hm; exact hm
  have hOav : artifactValidFor 6 o := by
    have hm := andR (andL (andL hv)); rw [hoi] at hm; exact andL hm
  have hMo : encodableSidecar o := by
    have hm := andR (andL he); rw [hoi] at hm; exact hm
  simp only [encodeEntry, hchunk, hsi, hti, hoi, decodeEntry, List.append_assoc]
  rw [decodeCommon_encodeCommon entry _ hp hk hb hd hr hord]
  simp only [bind, Option.bind]
  rw [dif_pos entry.predicate.property,
    chunked_roundTrip _ (by decide) entry c _ hchunk hav hMc]
  simp only [bind, Option.bind]
  rw [sidecar_roundTrip _ (by decide) i _ hSav hMs]
  simp only [bind, Option.bind]
  rw [sidecar_roundTrip _ (by decide) t _ hTav hMt]
  simp only [bind, Option.bind]
  rw [sidecar_roundTrip _ (by decide) o _ hOav hMo]
  simp only [bind, Option.bind, Option.some.injEq, Prod.mk.injEq, and_true]
  exact entry_rebuild entry (some c) (some i) (some t) (some o) none "" [] hchunk hsi hti hoi hl
    hsc hg entry.predicate.property

theorem decodeEntry_encodeEntry_quad (entry : Entry) (rest : List UInt8)
    (hv : entryValid 7 entry) (he : encodableEntry 7 entry) :
    decodeEntry 7 (encodeEntry 7 entry ++ rest) = some (entry, rest) := by
  obtain ⟨hp, hk, hb, hr, hord, hd⟩ := encodableEntry_common 7 entry he
  have hav : artifactValidFor 7 entry.artifact := andR (andL (andL (andL (andL (andL hv)))))
  obtain ⟨c, hchunk⟩ : ∃ c, entry.artifact.chunked = some c := by
    cases h : entry.artifact.chunked with
    | some c => exact ⟨c, rfl⟩
    | none => have hm := andR hav; rw [h] at hm; simp at hm
  have hs : entry.subjectIndex = none := by
    cases h : entry.subjectIndex with
    | none => rfl
    | some x => have hm := andR (andL (andL (andL (andL hv)))); rw [h] at hm; simp at hm
  have ht : entry.termIndex = none := by
    cases h : entry.termIndex with
    | none => rfl
    | some x => have hm := andR (andL (andL (andL hv))); rw [h] at hm; simp at hm
  have hoi : entry.objectIndex = none := by
    cases h : entry.objectIndex with
    | none => rfl
    | some x => have hm := andR (andL (andL hv)); rw [h] at hm; simp at hm
  obtain ⟨k, hl⟩ : ∃ k, entry.blockLayout = some k := by
    cases h : entry.blockLayout with
    | some k => exact ⟨k, rfl⟩
    | none => have hm := andR (andL hv); rw [h] at hm; simp at hm
  have hq := andR hv
  have hgadm : entry.graphSet.all graphNameAdmitted := andR (andL (andR hq))
  have hMc : encodableChunked c := by
    have hm := andR (andL (andL (andL (andL he)))); rw [hchunk] at hm; exact hm
  have hMbl : (fitsU32 entry.blankNodeScope.toUTF8.size && fitsU32 entry.graphSet.length &&
      entry.graphSet.all graphNameEncodable) = true := by
    have hm := andR he; rw [hl] at hm; exact hm
  simp only [encodeEntry, hchunk, hl, decodeEntry, List.append_assoc]
  rw [decodeCommon_encodeCommon entry _ hp hk hb hd hr hord]
  simp only [bind, Option.bind]
  rw [dif_pos entry.predicate.property,
    chunked_roundTrip _ (by decide) entry c _ hchunk hav hMc]
  simp only [bind, Option.bind]
  rw [decodeQuadTail_encodeQuadTail k entry.blankNodeScope entry.graphSet _
    (andL (andL hMbl)) (andR (andL hMbl)) (andR hMbl) hgadm]
  simp only [bind, Option.bind, Option.some.injEq, Prod.mk.injEq, and_true]
  exact entry_rebuild entry (some c) none none none (some k) entry.blankNodeScope entry.graphSet
    hchunk hs ht hoi hl rfl rfl entry.predicate.property

/-- Every admitted entry round-trips, in every wire version. -/
theorem decodeEntry_encodeEntry (version : Nat) (entry : Entry) (rest : List UInt8)
    (hv : entryValid version entry) (he : encodableEntry version entry) :
    decodeEntry version (encodeEntry version entry ++ rest) = some (entry, rest) := by
  match version with
  | 0 => exact decodeEntry_encodeEntry_v0 entry rest hv he
  | 1 => exact decodeEntry_encodeEntry_chunkedOnly 1 (Or.inl rfl) entry rest hv he
  | 2 => exact decodeEntry_encodeEntry_chunkedOnly 2 (Or.inr rfl) entry rest hv he
  | 3 => exact decodeEntry_encodeEntry_subject entry rest hv he
  | 4 => exact decodeEntry_encodeEntry_subjectTerm 4 (Or.inl rfl) entry rest hv he
  | 5 => exact decodeEntry_encodeEntry_subjectTerm 5 (Or.inr rfl) entry rest hv he
  | 6 => exact decodeEntry_encodeEntry_object entry rest hv he
  | 7 => exact decodeEntry_encodeEntry_quad entry rest hv he
  | n + 8 =>
      exact absurd (andR (andR (andL (andL (andL (andL (andL hv))))))) (by simp)

/-! ## The entry list -/

theorem decodeEntries_flatMap (version : Nat) : ∀ (entries : List Entry) (rest : List UInt8),
    entries.all (entryValid version) → entries.all (encodableEntry version) →
    decodeEntries version entries.length (entries.flatMap (encodeEntry version) ++ rest) =
      some (entries, rest) := by
  intro entries
  induction entries with
  | nil => intro rest _ _; simp [decodeEntries]
  | cons entry tail ih =>
      intro rest hv he
      simp only [List.all_cons, Bool.and_eq_true] at hv he
      simp only [List.length_cons, List.flatMap_cons, List.append_assoc, decodeEntries]
      rw [decodeEntry_encodeEntry version entry _ hv.1 he.1]
      simp only [bind, Option.bind]
      rw [ih rest hv.2 he.2]

/-! ## The manifest

`encode?` writes the magic, the version byte, the length-prefixed source
identity, the term-registry version, the layout label, SBM7's publication
profile, the entry count and the entries. `decode?` reads them back, re-runs
`valid`, and refuses trailing bytes. -/

/-- The entry list at the end of a manifest, with no trailing bytes. -/
theorem decodeEntries_flatMap_nil (version : Nat) (entries : List Entry)
    (hv : entries.all (entryValid version)) (he : entries.all (encodableEntry version)) :
    decodeEntries version entries.length (entries.flatMap (encodeEntry version)) =
      some (entries, []) := by
  have h := decodeEntries_flatMap version entries [] hv he
  simpa using h

/-! ### The version byte

Only the eight admitted versions are written, so the decoder's rejection test
is false and its `toNat` is exact. Both are decided one version at a time,
here, so the manifest proof itself does not split. -/

theorem versionByte_toNat (v : Nat) (h : v ≤ 7) : (UInt8.ofNat v).toNat = v := by
  match v, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => decide
  | (n + 8), h => exact absurd h (by omega)

theorem versionByte_admitted (v : Nat) (h : v ≤ 7) :
    (UInt8.ofNat v != wireVersion0 && UInt8.ofNat v != wireVersion1 &&
      UInt8.ofNat v != wireVersion2 && UInt8.ofNat v != wireVersion3 &&
      UInt8.ofNat v != wireVersion4 && UInt8.ofNat v != wireVersion5 &&
      UInt8.ofNat v != wireVersion6 && UInt8.ofNat v != wireVersion7) = false := by
  match v, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => decide
  | (n + 8), h => exact absurd h (by omega)

theorem versionByte_is7 (v : Nat) (h : v ≤ 7) :
    (UInt8.ofNat v == wireVersion7) = (v == 7) := by
  match v, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => decide
  | (n + 8), h => exact absurd h (by omega)

theorem decode?_encode? (manifest : Manifest) (bytes : ByteArray)
    (h : encode? manifest = some bytes) : decode? bytes = some manifest := by
  by_cases hgate : (valid manifest && encodable manifest) = true
  case neg => rw [encode?, if_neg hgate] at h; simp at h
  rw [encode?, if_pos hgate] at h
  have hvalid : valid manifest := andL hgate
  have hencodable : encodable manifest := andR hgate
  have hverLe : manifest.version ≤ 7 := by
    have hv := andL (andL (andL (andL (andL (andL (andL hvalid))))))
    simp only [Bool.or_eq_true, beq_iff_eq] at hv
    omega
  have hsid : fitsU32 manifest.sourceIdentity.size := andL (andL (andL (andL (andL hencodable))))
  have htrv : fitsU32 manifest.termRegistryVersion.toUTF8.size :=
    andR (andL (andL (andL (andL hencodable))))
  have hlay : fitsU32 manifest.layout.toUTF8.size := andR (andL (andL (andL hencodable)))
  have hprof : fitsU32 manifest.blankNodeProfile.toUTF8.size := andR (andL (andL hencodable))
  have hcount : fitsU32 manifest.entries.length := andR (andL hencodable)
  have hentriesEnc : manifest.entries.all (encodableEntry manifest.version) := andR hencodable
  have hentriesVal : manifest.entries.all (entryValid manifest.version) := andR hvalid
  have hsize : UInt32.size = 4294967296 := rfl
  have hsl2 : manifest.sourceIdentity.size < UInt32.size := by
    have h' : manifest.sourceIdentity.size < 4294967296 := by simpa [fitsU32] using hsid
    omega
  have hn : manifest.entries.length < UInt32.size := by
    have h' : manifest.entries.length < 4294967296 := by simpa [fitsU32] using hcount
    omega
  obtain rfl : bytes = byteArrayOfList _ := (Option.some.inj h).symm
  rw [decode?, listOfByteArray_byteArrayOfList]
  simp only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append,
    readU32LE_writeU32LE_append, parseU8_cons, bind, Option.bind,
    bne_self_eq_false, Bool.false_eq_true, if_false,
    drop4_writeU32LE, versionByte_admitted _ hverLe, versionByte_toNat _ hverLe,
    versionByte_is7 _ hverLe]
  rw [takeExact_of_length manifest.sourceIdentity.toList _ _
    (by rw [length_toList, u32_toNat_ofNat_of_lt hsl2])]
  simp only [bind, Option.bind]
  rw [decodeString_encodeString _ _ htrv]
  simp only [bind, Option.bind]
  rw [decodeString_encodeString _ _ hlay]
  simp only [bind, Option.bind]
  by_cases h7 : manifest.version = 7
  · rw [h7] at hentriesEnc hentriesVal ⊢
    simp only [beq_self_eq_true, if_true]
    rw [decodeString_encodeString _ _ hprof]
    simp only [bind, Option.bind, readU32LE_writeU32LE_append,
      u32_toNat_ofNat_of_lt hn, drop4_writeU32LE]
    rw [decodeEntries_flatMap_nil _ manifest.entries hentriesVal hentriesEnc]
    simp only [bind, Option.bind, List.isEmpty_nil, Bool.true_and, byteArrayOfList_toList]
    rw [show (7 : Nat) = manifest.version from h7.symm]
    simp only [hvalid, if_true]
  · have hprofEmpty : manifest.blankNodeProfile = "" := by
      have hq := andR (andL (andL (andL (andL (andL hvalid)))))
      rw [if_neg (by simp [h7])] at hq
      simpa using hq
    simp only [show (manifest.version == 7) = false from by simp [h7], Bool.false_eq_true,
      if_false, List.nil_append, bind, Option.bind, readU32LE_writeU32LE_append,
      u32_toNat_ofNat_of_lt hn, drop4_writeU32LE]
    rw [decodeEntries_flatMap_nil _ manifest.entries hentriesVal hentriesEnc]
    simp only [bind, Option.bind, List.isEmpty_nil, Bool.true_and, byteArrayOfList_toList,
      ← hprofEmpty]
    simp only [hvalid, if_true]

#print axioms decodeString_encodeString
#print axioms decodeGraphNames_flatMap
#print axioms decodeEntry_encodeEntry
#print axioms decodeEntries_flatMap
#print axioms decode?_encode?

end L4Factoidal.Storage.ShardManifest
