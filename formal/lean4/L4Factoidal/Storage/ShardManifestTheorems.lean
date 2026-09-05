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
  have hc : encodableCommon entry = true :=
    andL (andL (andL (andL (andL (andL (andL he))))))
  simp only [encodableCommon, Bool.and_eq_true, beq_iff_eq] at hc
  exact ⟨hc.1.1.1.1.1, hc.1.1.1.1.2, hc.1.1.1.2, hc.1.1.2, hc.1.2, hc.2⟩

/-- The reconstruction step: the record `decodeEntry` builds from decoded
    fields is the entry that produced them. -/
theorem entry_rebuild (entry : Entry) (chunked : Option ChunkedArtifact.Ref)
    (subjectIndex termIndex objectIndex literalIndex geoIndex : Option ArtifactRef)
    (blockLayout : Option BlockLayout) (scope : String) (names : List GraphName)
    (blobRefs : List Nat) (subjectZone objectZone : Option (List UInt8 × List UInt8))
    (hc : entry.artifact.chunked = chunked) (hs : entry.subjectIndex = subjectIndex)
    (ht : entry.termIndex = termIndex) (ho : entry.objectIndex = objectIndex)
    (hli : entry.literalIndex = literalIndex) (hgi : entry.geoIndex = geoIndex)
    (hl : entry.blockLayout = blockLayout) (hsc : entry.blankNodeScope = scope)
    (hg : entry.graphSet = names) (hbr : entry.blobRefs = blobRefs)
    (hsz : entry.subjectZone = subjectZone) (hoz : entry.objectZone = objectZone)
    (h : isIri entry.predicate.val) :
    ({ predicate := ⟨entry.predicate.val, h⟩
       artifact := { key := { value := entry.artifact.key.value }, bytes := entry.artifact.bytes,
                     sha256 := byteArrayOfList entry.artifact.sha256.toList, chunked := chunked }
       subjectIndex := subjectIndex
       termIndex := termIndex
       objectIndex := objectIndex
       literalIndex := literalIndex
       geoIndex := geoIndex
       blockLayout := blockLayout
       blankNodeScope := scope
       graphSet := names
       blobRefs := blobRefs
       subjectZone := subjectZone
       objectZone := objectZone
       rows := entry.rows
       ordinal := entry.ordinal } : Entry) = entry := by
  rw [byteArrayOfList_toList, ← hc, ← hs, ← ht, ← ho, ← hli, ← hgi, ← hl, ← hsc, ← hg,
    ← hbr, ← hsz, ← hoz]

/-! ### Reading the two admission gates

`entryValid` and `encodableEntry` are left-associated Boolean conjunctions, so
each conjunct is reached by a chain of `andL`/`andR`. The version-dependent
conjuncts are `match` expressions; with a literal version and a known option
shape they reduce, so `exact` on the reduced form suffices. -/

/-- One index sidecar round-trips under the manifest's own two gates. -/
theorem sidecar_roundTrip (version : Nat)
    (hversion : version = 3 ∨ version = 4 ∨ version = 5 ∨ version = 6 ∨ version = 8 ∨
      version = 9 ∨ version = 10)
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
    rcases hversion with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simpa using andR h
  exact decodeSidecarRef_encodeSidecarRef index c rest hc hkey hbytes hsha
    (andL (andL hmc)) (andR (andL hmc)) (by simpa using andR hmc) htotal

/-- The primary artifact's chunk commitment round-trips under the same two
    gates. -/
theorem chunked_roundTrip (version : Nat)
    (hversion : version = 1 ∨ version = 2 ∨ version = 3 ∨ version = 4 ∨ version = 5 ∨
      version = 6 ∨ version = 7 ∨ version = 8 ∨ version = 9 ∨ version = 10)
    (entry : Entry) (c : ChunkedArtifact.Ref) (rest : List UInt8)
    (hc : entry.artifact.chunked = some c)
    (hav : artifactValidFor version entry.artifact) (hen : encodableChunked c) :
    decodeChunkedRef entry.artifact.bytes (encodeChunkedRef c ++ rest) = some (c, rest) := by
  have htotal : c.totalBytes = entry.artifact.bytes := by
    have h := andR hav
    rw [hc] at h
    rcases hversion with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa using andR h
  exact decodeChunkedRef_encodeChunkedRef c entry.artifact.bytes rest
    (andL (andL hen)) (andR (andL hen)) (by simpa using andR hen) htotal

/-! ## SBM10 fields: the byte string, the zone map, the blob references

The zone bounds are PREFIXES of keys, so the order the manifest states over
them must survive taking a prefix of a fixed length. `lexLe_take` is that
property and `zoneMap_sound` is its use. -/

/-- Taking the same number of leading bytes off both sides preserves the
    lexicographic order. This is what makes a truncated zone bound sound. -/
theorem lexLe_take : ∀ (n : Nat) (a b : List UInt8), lexLe a b = true →
    lexLe (a.take n) (b.take n) = true := by
  intro n
  induction n with
  | zero => intro a b _; simp [lexLe]
  | succ n ih =>
      intro a b h
      cases a with
      | nil => simp [lexLe]
      | cons x xs =>
          cases b with
          | nil => simp [lexLe] at h
          | cons y ys =>
              simp only [List.take_succ_cons, lexLe]
              simp only [lexLe] at h
              by_cases hxy : x < y
              · simp [hxy]
              · simp only [hxy, if_false] at h ⊢
                by_cases heq : x == y
                · simp only [heq, if_true] at h ⊢
                  exact ih xs ys h
                · simp only [heq, if_false] at h; exact absurd h (by simp)

/-- **The zone-map gate.** A key at or above the block's smallest key and at or
    below its largest is inside the entry's truncated bounds, so a planner that
    drops an entry on this test never drops a block that holds a matching
    row. -/
theorem zoneMap_sound (lower upper key : List UInt8)
    (hlower : lexLe lower key = true) (hupper : lexLe key upper = true) :
    zoneMayContain (lower.take zoneBytes, upper.take zoneBytes) key = true := by
  simp only [zoneMayContain, Bool.and_eq_true]
  exact ⟨lexLe_take zoneBytes lower key hlower, lexLe_take zoneBytes key upper hupper⟩

/-- Below version 10 the three per-entry SBM10 fields are absent. -/
theorem sbm10EntryFields_absent (version : Nat) (entry : Entry)
    (hne : (version == 10) = false) (h : sbm10EntryFields version entry = true) :
    entry.blobRefs = [] ∧ entry.subjectZone = none ∧ entry.objectZone = none := by
  rw [sbm10EntryFields, if_neg (by simp [hne])] at h
  refine ⟨?_, ?_, ?_⟩
  · simpa using andL (andL h)
  · have h2 : entry.subjectZone.isNone = true := andR (andL h)
    simpa using h2
  · have h3 : entry.objectZone.isNone = true := andR h
    simpa using h3

/-- A length-prefixed byte string round-trips. Unlike `encodeString` it makes
    no UTF-8 claim: a zone bound is a prefix of a key. -/
theorem decodeBytesField_encodeBytesField (xs rest : List UInt8) (h : fitsU32 xs.length) :
    decodeBytesField (encodeBytesField xs ++ rest) = some (xs, rest) := by
  have hlt : xs.length < UInt32.size := by
    have h' : xs.length < 4294967296 := by simpa [fitsU32] using h
    have hsize : UInt32.size = 4294967296 := rfl
    omega
  rw [encodeBytesField, decodeBytesField]
  simp only [List.append_assoc, bind, Option.bind, readU32LE_writeU32LE_append,
    u32_toNat_ofNat_of_lt hlt, drop4_writeU32LE]
  exact takeExact_append xs rest

theorem decodeZone_encodeZone (zone : List UInt8 × List UInt8) (rest : List UInt8)
    (hlower : fitsU32 zone.1.length) (hupper : fitsU32 zone.2.length) :
    decodeZone (encodeZone zone ++ rest) = some (zone, rest) := by
  rw [encodeZone, decodeZone]
  simp only [List.append_assoc, bind, Option.bind]
  rw [decodeBytesField_encodeBytesField _ _ hlower]
  simp only [bind, Option.bind]
  rw [decodeBytesField_encodeBytesField _ _ hupper]

/-- A zone bound of at most `zoneBytes` bytes is within the u32 field width. -/
theorem fitsU32_of_le_zoneBytes {n : Nat} (h : n ≤ zoneBytes) : fitsU32 n := by
  simp only [zoneBytes] at h
  simp only [fitsU32, decide_eq_true_eq]
  omega

theorem decodeBlobRefList_flatMap : ∀ (indices : List Nat) (rest : List UInt8),
    indices.all fitsU32 = true →
    decodeBlobRefList indices.length
        (indices.flatMap (fun index => writeU32LE (UInt32.ofNat index)) ++ rest) =
      some (indices, rest) := by
  intro indices
  induction indices with
  | nil => intro rest _; simp [decodeBlobRefList]
  | cons index tail ih =>
      intro rest h
      simp only [List.all_cons, Bool.and_eq_true] at h
      have hlt : index < UInt32.size := by
        have h' : index < 4294967296 := by simpa [fitsU32] using h.1
        have hsize : UInt32.size = 4294967296 := rfl
        omega
      simp only [List.length_cons, List.flatMap_cons, List.append_assoc, decodeBlobRefList,
        bind, Option.bind, readU32LE_writeU32LE_append, u32_toNat_ofNat_of_lt hlt]
      rw [takeExact_of_length (writeU32LE (UInt32.ofNat index)) _ 4 (by simp)]
      simp only [bind, Option.bind]
      rw [ih rest h.2]

theorem decodeBlobRefs_encodeBlobRefs (indices : List Nat) (rest : List UInt8)
    (hcount : fitsU32 indices.length) (hall : indices.all fitsU32 = true) :
    decodeBlobRefs (encodeBlobRefs indices ++ rest) = some (indices, rest) := by
  have hlt : indices.length < UInt32.size := by
    have h' : indices.length < 4294967296 := by simpa [fitsU32] using hcount
    have hsize : UInt32.size = 4294967296 := rfl
    omega
  rw [encodeBlobRefs, decodeBlobRefs]
  simp only [List.append_assoc, bind, Option.bind, readU32LE_writeU32LE_append,
    u32_toNat_ofNat_of_lt hlt]
  rw [takeExact_of_length (writeU32LE (UInt32.ofNat indices.length)) _ 4 (by simp)]
  simp only [bind, Option.bind]
  exact decodeBlobRefList_flatMap indices rest hall

theorem decodeBlobList_flatMap : ∀ (blobs : List ArtifactRef) (rest : List UInt8),
    blobs.all (artifactValidFor 10) = true → blobs.all encodableSidecar = true →
    decodeBlobList blobs.length (blobs.flatMap encodeSidecarRef ++ rest) =
      some (blobs, rest) := by
  intro blobs
  induction blobs with
  | nil => intro rest _ _; simp [decodeBlobList]
  | cons blob tail ih =>
      intro rest hv he
      simp only [List.all_cons, Bool.and_eq_true] at hv he
      simp only [List.length_cons, List.flatMap_cons, List.append_assoc, decodeBlobList]
      rw [sidecar_roundTrip 10 (by decide) blob _ hv.1 he.1]
      simp only [bind, Option.bind]
      rw [ih rest hv.2 he.2]

theorem decodeBlobTable_encodeBlobTable (blobs : List ArtifactRef) (rest : List UInt8)
    (hcount : fitsU32 blobs.length) (hv : blobs.all (artifactValidFor 10) = true)
    (he : blobs.all encodableSidecar = true) :
    decodeBlobTable (encodeBlobTable blobs ++ rest) = some (blobs, rest) := by
  have hlt : blobs.length < UInt32.size := by
    have h' : blobs.length < 4294967296 := by simpa [fitsU32] using hcount
    have hsize : UInt32.size = 4294967296 := rfl
    omega
  rw [encodeBlobTable, decodeBlobTable]
  simp only [List.append_assoc, bind, Option.bind, readU32LE_writeU32LE_append,
    u32_toNat_ofNat_of_lt hlt]
  rw [takeExact_of_length (writeU32LE (UInt32.ofNat blobs.length)) _ 4 (by simp)]
  simp only [bind, Option.bind]
  exact decodeBlobList_flatMap blobs rest hv he

/-! ### The entry round trip, one wire-version shape at a time

Five shapes cover the eight versions: no commitment (SBM0), a chunk commitment
(SBM1/SBM2), plus a subject sidecar (SBM3), plus a term sidecar (SBM4/SBM5),
plus an object sidecar (SBM6), and the chunk commitment plus the quad tail with
no sidecar (SBM7). -/

theorem decodeEntry_encodeEntry_v0 (entry : Entry) (rest : List UInt8)
    (hv : entryValid 0 entry) (he : encodableEntry 0 entry) :
    decodeEntry 0 (encodeEntry 0 entry ++ rest) = some (entry, rest) := by
  obtain ⟨hp, hk, hb, hr, hord, hd⟩ := encodableEntry_common 0 entry he
  obtain ⟨hbr, hsz, hoz⟩ := sbm10EntryFields_absent _ entry (by decide) (andR hv)
  have hv := andL hv
  have he := andL he
  have hav : artifactValidFor 0 entry.artifact := andR (andL (andL (andL (andL (andL (andL hv))))))
  have hchunk : entry.artifact.chunked = none := by
    cases h : entry.artifact.chunked with
    | none => rfl
    | some c => have hm := andR hav; rw [h] at hm; simp at hm
  have hs : entry.subjectIndex = none := by
    cases h : entry.subjectIndex with
    | none => rfl
    | some i => have hm := andR (andL (andL (andL (andL (andL hv))))); rw [h] at hm; simp at hm
  have ht : entry.termIndex = none := by
    cases h : entry.termIndex with
    | none => rfl
    | some i => have hm := andR (andL (andL (andL (andL hv)))); rw [h] at hm; simp at hm
  have hoi : entry.objectIndex = none := by
    cases h : entry.objectIndex with
    | none => rfl
    | some i => have hm := andR (andL (andL (andL hv))); rw [h] at hm; simp at hm
  have hlg : entry.literalIndex = none ∧ entry.geoIndex = none := by
    have hm := andR (andL (andL hv))
    cases h1 : entry.literalIndex with
    | none =>
        cases h2 : entry.geoIndex with
        | none => exact ⟨rfl, rfl⟩
        | some y => rw [h1, h2] at hm; simp at hm
    | some x =>
        cases h2 : entry.geoIndex with
        | none => rw [h1, h2] at hm; simp at hm
        | some y => rw [h1, h2] at hm; simp at hm
  have hli : entry.literalIndex = none := hlg.1
  have hgi : entry.geoIndex = none := hlg.2
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
  exact entry_rebuild entry none none none none none none none "" [] [] none none hchunk hs ht
    hoi hli hgi hl hsc hg hbr hsz hoz entry.predicate.property

theorem decodeEntry_encodeEntry_chunkedOnly (version : Nat)
    (hversion : version = 1 ∨ version = 2) (entry : Entry) (rest : List UInt8)
    (hv : entryValid version entry) (he : encodableEntry version entry) :
    decodeEntry version (encodeEntry version entry ++ rest) = some (entry, rest) := by
  rcases hversion with rfl | rfl
  all_goals (
    obtain ⟨hp, hk, hb, hr, hord, hd⟩ := encodableEntry_common _ entry he
    obtain ⟨hbr, hsz, hoz⟩ := sbm10EntryFields_absent _ entry (by decide) (andR hv)
    have hv := andL hv
    have he := andL he
    have hav : artifactValidFor _ entry.artifact := andR (andL (andL (andL (andL (andL (andL hv))))))
    obtain ⟨c, hchunk⟩ : ∃ c, entry.artifact.chunked = some c := by
      cases h : entry.artifact.chunked with
      | some c => exact ⟨c, rfl⟩
      | none => have hm := andR hav; rw [h] at hm; simp at hm
    have hs : entry.subjectIndex = none := by
      cases h : entry.subjectIndex with
      | none => rfl
      | some i => have hm := andR (andL (andL (andL (andL (andL hv))))); rw [h] at hm; simp at hm
    have ht : entry.termIndex = none := by
      cases h : entry.termIndex with
      | none => rfl
      | some i => have hm := andR (andL (andL (andL (andL hv)))); rw [h] at hm; simp at hm
    have hoi : entry.objectIndex = none := by
      cases h : entry.objectIndex with
      | none => rfl
      | some i => have hm := andR (andL (andL (andL hv))); rw [h] at hm; simp at hm
    have hlg : entry.literalIndex = none ∧ entry.geoIndex = none := by
      have hm := andR (andL (andL hv))
      cases h1 : entry.literalIndex with
      | none =>
          cases h2 : entry.geoIndex with
          | none => exact ⟨rfl, rfl⟩
          | some y => rw [h1, h2] at hm; simp at hm
      | some x =>
          cases h2 : entry.geoIndex with
          | none => rw [h1, h2] at hm; simp at hm
          | some y => rw [h1, h2] at hm; simp at hm
    have hli : entry.literalIndex = none := hlg.1
    have hgi : entry.geoIndex = none := hlg.2
    have hl : entry.blockLayout = none := by
      cases h : entry.blockLayout with
      | none => rfl
      | some k => have hm := andR (andL hv); rw [h] at hm; simp at hm
    have hsc : entry.blankNodeScope = "" := by simpa using andL (andR hv)
    have hg : entry.graphSet = [] := by simpa using andR (andR hv)
    have hMc : encodableChunked c := by
      have hm := andR (andL (andL (andL (andL (andL he))))); rw [hchunk] at hm; exact hm
    simp only [encodeEntry, hchunk, decodeEntry, List.append_assoc]
    rw [decodeCommon_encodeCommon entry _ hp hk hb hd hr hord]
    simp only [bind, Option.bind]
    rw [dif_pos entry.predicate.property,
      chunked_roundTrip _ (by decide) entry c _ hchunk hav hMc]
    simp only [bind, Option.bind, Option.some.injEq, Prod.mk.injEq, and_true]
    exact entry_rebuild entry (some c) none none none none none none "" [] [] none none hchunk hs
      ht hoi hli hgi hl hsc hg hbr hsz hoz entry.predicate.property)

theorem decodeEntry_encodeEntry_subject (entry : Entry) (rest : List UInt8)
    (hv : entryValid 3 entry) (he : encodableEntry 3 entry) :
    decodeEntry 3 (encodeEntry 3 entry ++ rest) = some (entry, rest) := by
  obtain ⟨hp, hk, hb, hr, hord, hd⟩ := encodableEntry_common 3 entry he
  obtain ⟨hbr, hsz, hoz⟩ := sbm10EntryFields_absent _ entry (by decide) (andR hv)
  have hv := andL hv
  have he := andL he
  have hav : artifactValidFor 3 entry.artifact := andR (andL (andL (andL (andL (andL (andL hv))))))
  obtain ⟨c, hchunk⟩ : ∃ c, entry.artifact.chunked = some c := by
    cases h : entry.artifact.chunked with
    | some c => exact ⟨c, rfl⟩
    | none => have hm := andR hav; rw [h] at hm; simp at hm
  obtain ⟨i, hsi⟩ : ∃ i, entry.subjectIndex = some i := by
    cases h : entry.subjectIndex with
    | some i => exact ⟨i, rfl⟩
    | none => have hm := andR (andL (andL (andL (andL (andL hv))))); rw [h] at hm; simp at hm
  have ht : entry.termIndex = none := by
    cases h : entry.termIndex with
    | none => rfl
    | some x => have hm := andR (andL (andL (andL (andL hv)))); rw [h] at hm; simp at hm
  have hoi : entry.objectIndex = none := by
    cases h : entry.objectIndex with
    | none => rfl
    | some x => have hm := andR (andL (andL (andL hv))); rw [h] at hm; simp at hm
  have hl : entry.blockLayout = none := by
    cases h : entry.blockLayout with
    | none => rfl
    | some k => have hm := andR (andL hv); rw [h] at hm; simp at hm
  have hsc : entry.blankNodeScope = "" := by simpa using andL (andR hv)
  have hg : entry.graphSet = [] := by simpa using andR (andR hv)
  have hMc : encodableChunked c := by
    have hm := andR (andL (andL (andL (andL (andL he))))); rw [hchunk] at hm; exact hm
  have hlg : entry.literalIndex = none ∧ entry.geoIndex = none := by
    have hm := andR (andL (andL hv))
    cases h1 : entry.literalIndex with
    | none =>
        cases h2 : entry.geoIndex with
        | none => exact ⟨rfl, rfl⟩
        | some y => rw [h1, h2] at hm; simp at hm
    | some x =>
        cases h2 : entry.geoIndex with
        | none => rw [h1, h2] at hm; simp at hm
        | some y => rw [h1, h2] at hm; simp at hm
  have hli : entry.literalIndex = none := hlg.1
  have hgi : entry.geoIndex = none := hlg.2
  have hSav : artifactValidFor 3 i := by
    have hm := andR (andL (andL (andL (andL (andL hv))))); rw [hsi] at hm; exact andL hm
  have hMs : encodableSidecar i := by
    have hm := andR (andL (andL (andL (andL he)))); rw [hsi] at hm; exact hm
  simp only [encodeEntry, hchunk, hsi, ht, hoi, decodeEntry, List.append_assoc]
  rw [decodeCommon_encodeCommon entry _ hp hk hb hd hr hord]
  simp only [bind, Option.bind]
  rw [dif_pos entry.predicate.property,
    chunked_roundTrip _ (by decide) entry c _ hchunk hav hMc]
  simp only [bind, Option.bind]
  rw [sidecar_roundTrip _ (by decide) i _ hSav hMs]
  simp only [bind, Option.bind, Option.some.injEq, Prod.mk.injEq, and_true]
  exact entry_rebuild entry (some c) (some i) none none none none none "" [] [] none none hchunk
    hsi ht hoi hli hgi hl hsc hg hbr hsz hoz entry.predicate.property

theorem decodeEntry_encodeEntry_subjectTerm (version : Nat)
    (hversion : version = 4 ∨ version = 5) (entry : Entry) (rest : List UInt8)
    (hv : entryValid version entry) (he : encodableEntry version entry) :
    decodeEntry version (encodeEntry version entry ++ rest) = some (entry, rest) := by
  rcases hversion with rfl | rfl
  all_goals (
    obtain ⟨hp, hk, hb, hr, hord, hd⟩ := encodableEntry_common _ entry he
    obtain ⟨hbr, hsz, hoz⟩ := sbm10EntryFields_absent _ entry (by decide) (andR hv)
    have hv := andL hv
    have he := andL he
    have hav : artifactValidFor _ entry.artifact := andR (andL (andL (andL (andL (andL (andL hv))))))
    obtain ⟨c, hchunk⟩ : ∃ c, entry.artifact.chunked = some c := by
      cases h : entry.artifact.chunked with
      | some c => exact ⟨c, rfl⟩
      | none => have hm := andR hav; rw [h] at hm; simp at hm
    obtain ⟨i, hsi⟩ : ∃ i, entry.subjectIndex = some i := by
      cases h : entry.subjectIndex with
      | some i => exact ⟨i, rfl⟩
      | none => have hm := andR (andL (andL (andL (andL (andL hv))))); rw [h] at hm; simp at hm
    obtain ⟨t, hti⟩ : ∃ t, entry.termIndex = some t := by
      cases h : entry.termIndex with
      | some t => exact ⟨t, rfl⟩
      | none => have hm := andR (andL (andL (andL (andL hv)))); rw [h] at hm; simp at hm
    have hoi : entry.objectIndex = none := by
      cases h : entry.objectIndex with
      | none => rfl
      | some x => have hm := andR (andL (andL (andL hv))); rw [h] at hm; simp at hm
    have hl : entry.blockLayout = none := by
      cases h : entry.blockLayout with
      | none => rfl
      | some k => have hm := andR (andL hv); rw [h] at hm; simp at hm
    have hsc : entry.blankNodeScope = "" := by simpa using andL (andR hv)
    have hg : entry.graphSet = [] := by simpa using andR (andR hv)
    have hMc : encodableChunked c := by
      have hm := andR (andL (andL (andL (andL (andL he))))); rw [hchunk] at hm; exact hm
    have hlg : entry.literalIndex = none ∧ entry.geoIndex = none := by
      have hm := andR (andL (andL hv))
      cases h1 : entry.literalIndex with
      | none =>
          cases h2 : entry.geoIndex with
          | none => exact ⟨rfl, rfl⟩
          | some y => rw [h1, h2] at hm; simp at hm
      | some x =>
          cases h2 : entry.geoIndex with
          | none => rw [h1, h2] at hm; simp at hm
          | some y => rw [h1, h2] at hm; simp at hm
    have hli : entry.literalIndex = none := hlg.1
    have hgi : entry.geoIndex = none := hlg.2
    have hms := andR (andL (andL (andL (andL (andL hv)))))
    rw [hsi] at hms
    have hSav := andL hms
    have hMs : encodableSidecar i := by
      have hm := andR (andL (andL (andL (andL he)))); rw [hsi] at hm; exact hm
    have hmt := andR (andL (andL (andL (andL hv))))
    rw [hti] at hmt
    have hTav := andL hmt
    have hMt : encodableSidecar t := by
      have hm := andR (andL (andL (andL he))); rw [hti] at hm; exact hm
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
    exact entry_rebuild entry (some c) (some i) (some t) none none none none "" [] [] none none
      hchunk hsi hti hoi hli hgi hl hsc hg hbr hsz hoz entry.predicate.property)

theorem decodeEntry_encodeEntry_object (entry : Entry) (rest : List UInt8)
    (hv : entryValid 6 entry) (he : encodableEntry 6 entry) :
    decodeEntry 6 (encodeEntry 6 entry ++ rest) = some (entry, rest) := by
  obtain ⟨hp, hk, hb, hr, hord, hd⟩ := encodableEntry_common 6 entry he
  obtain ⟨hbr, hsz, hoz⟩ := sbm10EntryFields_absent _ entry (by decide) (andR hv)
  have hv := andL hv
  have he := andL he
  have hav : artifactValidFor 6 entry.artifact := andR (andL (andL (andL (andL (andL (andL hv))))))
  obtain ⟨c, hchunk⟩ : ∃ c, entry.artifact.chunked = some c := by
    cases h : entry.artifact.chunked with
    | some c => exact ⟨c, rfl⟩
    | none => have hm := andR hav; rw [h] at hm; simp at hm
  obtain ⟨i, hsi⟩ : ∃ i, entry.subjectIndex = some i := by
    cases h : entry.subjectIndex with
    | some i => exact ⟨i, rfl⟩
    | none => have hm := andR (andL (andL (andL (andL (andL hv))))); rw [h] at hm; simp at hm
  obtain ⟨t, hti⟩ : ∃ t, entry.termIndex = some t := by
    cases h : entry.termIndex with
    | some t => exact ⟨t, rfl⟩
    | none => have hm := andR (andL (andL (andL (andL hv)))); rw [h] at hm; simp at hm
  obtain ⟨o, hoi⟩ : ∃ o, entry.objectIndex = some o := by
    cases h : entry.objectIndex with
    | some o => exact ⟨o, rfl⟩
    | none => have hm := andR (andL (andL (andL hv))); rw [h] at hm; simp at hm
  have hl : entry.blockLayout = none := by
    cases h : entry.blockLayout with
    | none => rfl
    | some k => have hm := andR (andL hv); rw [h] at hm; simp at hm
  have hsc : entry.blankNodeScope = "" := by simpa using andL (andR hv)
  have hg : entry.graphSet = [] := by simpa using andR (andR hv)
  have hMc : encodableChunked c := by
    have hm := andR (andL (andL (andL (andL (andL he))))); rw [hchunk] at hm; exact hm
  have hlg : entry.literalIndex = none ∧ entry.geoIndex = none := by
    have hm := andR (andL (andL hv))
    cases h1 : entry.literalIndex with
    | none =>
        cases h2 : entry.geoIndex with
        | none => exact ⟨rfl, rfl⟩
        | some y => rw [h1, h2] at hm; simp at hm
    | some x =>
        cases h2 : entry.geoIndex with
        | none => rw [h1, h2] at hm; simp at hm
        | some y => rw [h1, h2] at hm; simp at hm
  have hli : entry.literalIndex = none := hlg.1
  have hgi : entry.geoIndex = none := hlg.2
  have hSav : artifactValidFor 6 i := by
    have hm := andR (andL (andL (andL (andL (andL hv))))); rw [hsi] at hm; exact andL hm
  have hMs : encodableSidecar i := by
    have hm := andR (andL (andL (andL (andL he)))); rw [hsi] at hm; exact hm
  have hTav : artifactValidFor 6 t := by
    have hm := andR (andL (andL (andL (andL hv)))); rw [hti] at hm; exact andL hm
  have hMt : encodableSidecar t := by
    have hm := andR (andL (andL (andL he))); rw [hti] at hm; exact hm
  have hOav : artifactValidFor 6 o := by
    have hm := andR (andL (andL (andL hv))); rw [hoi] at hm; exact andL hm
  have hMo : encodableSidecar o := by
    have hm := andR (andL (andL he)); rw [hoi] at hm; exact hm
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
  exact entry_rebuild entry (some c) (some i) (some t) (some o) none none none "" [] [] none none
    hchunk hsi hti hoi hli hgi hl hsc hg hbr hsz hoz entry.predicate.property

theorem decodeEntry_encodeEntry_quad (entry : Entry) (rest : List UInt8)
    (hv : entryValid 7 entry) (he : encodableEntry 7 entry) :
    decodeEntry 7 (encodeEntry 7 entry ++ rest) = some (entry, rest) := by
  obtain ⟨hp, hk, hb, hr, hord, hd⟩ := encodableEntry_common 7 entry he
  obtain ⟨hbr, hsz, hoz⟩ := sbm10EntryFields_absent _ entry (by decide) (andR hv)
  have hv := andL hv
  have he := andL he
  have hav : artifactValidFor 7 entry.artifact := andR (andL (andL (andL (andL (andL (andL hv))))))
  obtain ⟨c, hchunk⟩ : ∃ c, entry.artifact.chunked = some c := by
    cases h : entry.artifact.chunked with
    | some c => exact ⟨c, rfl⟩
    | none => have hm := andR hav; rw [h] at hm; simp at hm
  have hs : entry.subjectIndex = none := by
    cases h : entry.subjectIndex with
    | none => rfl
    | some x => have hm := andR (andL (andL (andL (andL (andL hv))))); rw [h] at hm; simp at hm
  have ht : entry.termIndex = none := by
    cases h : entry.termIndex with
    | none => rfl
    | some x => have hm := andR (andL (andL (andL (andL hv)))); rw [h] at hm; simp at hm
  have hoi : entry.objectIndex = none := by
    cases h : entry.objectIndex with
    | none => rfl
    | some x => have hm := andR (andL (andL (andL hv))); rw [h] at hm; simp at hm
  have hlg : entry.literalIndex = none ∧ entry.geoIndex = none := by
    have hm := andR (andL (andL hv))
    cases h1 : entry.literalIndex with
    | none =>
        cases h2 : entry.geoIndex with
        | none => exact ⟨rfl, rfl⟩
        | some y => rw [h1, h2] at hm; simp at hm
    | some x =>
        cases h2 : entry.geoIndex with
        | none => rw [h1, h2] at hm; simp at hm
        | some y => rw [h1, h2] at hm; simp at hm
  have hli : entry.literalIndex = none := hlg.1
  have hgi : entry.geoIndex = none := hlg.2
  obtain ⟨k, hl⟩ : ∃ k, entry.blockLayout = some k := by
    cases h : entry.blockLayout with
    | some k => exact ⟨k, rfl⟩
    | none => have hm := andR (andL hv); rw [h] at hm; simp at hm
  have hq := andR hv
  have hgadm : entry.graphSet.all graphNameAdmitted := andR (andL (andR hq))
  have hMc : encodableChunked c := by
    have hm := andR (andL (andL (andL (andL (andL he))))); rw [hchunk] at hm; exact hm
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
  exact entry_rebuild entry (some c) none none none none none (some k) entry.blankNodeScope
    entry.graphSet [] none none hchunk hs ht hoi hli hgi hl rfl rfl hbr hsz hoz
    entry.predicate.property


/-- SBM8 is SBM7 plus the LGI1 literal search index, written where SBM6 writes
    its object index. -/
theorem decodeEntry_encodeEntry_quadLiteral (entry : Entry) (rest : List UInt8)
    (hv : entryValid 8 entry) (he : encodableEntry 8 entry) :
    decodeEntry 8 (encodeEntry 8 entry ++ rest) = some (entry, rest) := by
  obtain ⟨hp, hk, hb, hr, hord, hd⟩ := encodableEntry_common 8 entry he
  obtain ⟨hbr, hsz, hoz⟩ := sbm10EntryFields_absent _ entry (by decide) (andR hv)
  have hv := andL hv
  have he := andL he
  have hav : artifactValidFor 8 entry.artifact :=
    andR (andL (andL (andL (andL (andL (andL hv))))))
  obtain ⟨c, hchunk⟩ : ∃ c, entry.artifact.chunked = some c := by
    cases h : entry.artifact.chunked with
    | some c => exact ⟨c, rfl⟩
    | none => have hm := andR hav; rw [h] at hm; simp at hm
  have hs : entry.subjectIndex = none := by
    cases h : entry.subjectIndex with
    | none => rfl
    | some x => have hm := andR (andL (andL (andL (andL (andL hv))))); rw [h] at hm; simp at hm
  have ht : entry.termIndex = none := by
    cases h : entry.termIndex with
    | none => rfl
    | some x => have hm := andR (andL (andL (andL (andL hv)))); rw [h] at hm; simp at hm
  have hoi : entry.objectIndex = none := by
    cases h : entry.objectIndex with
    | none => rfl
    | some x => have hm := andR (andL (andL (andL hv))); rw [h] at hm; simp at hm
  have hgi : entry.geoIndex = none := by
    cases h2 : entry.geoIndex with
    | none => rfl
    | some y =>
        have hm := andR (andL (andL hv))
        cases h1 : entry.literalIndex with
        | none => rw [h1, h2] at hm; simp at hm
        | some x => rw [h1, h2] at hm; simp at hm
  obtain ⟨l, hli⟩ : ∃ l, entry.literalIndex = some l := by
    cases h : entry.literalIndex with
    | some l => exact ⟨l, rfl⟩
    | none => have hm := andR (andL (andL hv)); rw [h, hgi] at hm; simp at hm
  obtain ⟨k, hl⟩ : ∃ k, entry.blockLayout = some k := by
    cases h : entry.blockLayout with
    | some k => exact ⟨k, rfl⟩
    | none => have hm := andR (andL hv); rw [h] at hm; simp at hm
  have hq := andR hv
  have hgadm : entry.graphSet.all graphNameAdmitted := andR (andL (andR hq))
  have hMc : encodableChunked c := by
    have hm := andR (andL (andL (andL (andL (andL he))))); rw [hchunk] at hm; exact hm
  have hLav : artifactValidFor 8 l := by
    have hm := andR (andL (andL hv)); rw [hli, hgi] at hm; exact andL hm
  have hMl : encodableSidecar l := by
    have hm := andR (andL he); rw [hli, hgi] at hm; exact hm
  have hMbl : (fitsU32 entry.blankNodeScope.toUTF8.size && fitsU32 entry.graphSet.length &&
      entry.graphSet.all graphNameEncodable) = true := by
    have hm := andR he; rw [hl] at hm; exact hm
  simp only [encodeEntry, hchunk, hl, hli, decodeEntry, List.append_assoc]
  rw [decodeCommon_encodeCommon entry _ hp hk hb hd hr hord]
  simp only [bind, Option.bind]
  rw [dif_pos entry.predicate.property,
    chunked_roundTrip _ (by decide) entry c _ hchunk hav hMc]
  simp only [bind, Option.bind]
  rw [sidecar_roundTrip _ (by decide) l _ hLav hMl]
  simp only [bind, Option.bind]
  rw [decodeQuadTail_encodeQuadTail k entry.blankNodeScope entry.graphSet _
    (andL (andL hMbl)) (andR (andL hMbl)) (andR hMbl) hgadm]
  simp only [bind, Option.bind, Option.some.injEq, Prod.mk.injEq, and_true]
  exact entry_rebuild entry (some c) none none none (some l) none (some k) entry.blankNodeScope
    entry.graphSet [] none none hchunk hs ht hoi hli hgi hl rfl rfl hbr hsz hoz
    entry.predicate.property

/-- SBM9 is SBM8 plus the GBI1 geometry bounding-box index, written
    immediately after the LGI1 sidecar and before the quad tail. -/
theorem decodeEntry_encodeEntry_quadGeo (entry : Entry) (rest : List UInt8)
    (hv : entryValid 9 entry) (he : encodableEntry 9 entry) :
    decodeEntry 9 (encodeEntry 9 entry ++ rest) = some (entry, rest) := by
  obtain ⟨hp, hk, hb, hr, hord, hd⟩ := encodableEntry_common 9 entry he
  obtain ⟨hbr, hsz, hoz⟩ := sbm10EntryFields_absent _ entry (by decide) (andR hv)
  have hv := andL hv
  have he := andL he
  have hav : artifactValidFor 9 entry.artifact :=
    andR (andL (andL (andL (andL (andL (andL hv))))))
  obtain ⟨c, hchunk⟩ : ∃ c, entry.artifact.chunked = some c := by
    cases h : entry.artifact.chunked with
    | some c => exact ⟨c, rfl⟩
    | none => have hm := andR hav; rw [h] at hm; simp at hm
  have hs : entry.subjectIndex = none := by
    cases h : entry.subjectIndex with
    | none => rfl
    | some x => have hm := andR (andL (andL (andL (andL (andL hv))))); rw [h] at hm; simp at hm
  have ht : entry.termIndex = none := by
    cases h : entry.termIndex with
    | none => rfl
    | some x => have hm := andR (andL (andL (andL (andL hv)))); rw [h] at hm; simp at hm
  have hoi : entry.objectIndex = none := by
    cases h : entry.objectIndex with
    | none => rfl
    | some x => have hm := andR (andL (andL (andL hv))); rw [h] at hm; simp at hm
  obtain ⟨l, g, hli, hgi⟩ :
      ∃ l g, entry.literalIndex = some l ∧ entry.geoIndex = some g := by
    have hm := andR (andL (andL hv))
    cases h1 : entry.literalIndex with
    | none =>
        cases h2 : entry.geoIndex with
        | none => rw [h1, h2] at hm; simp at hm
        | some y => rw [h1, h2] at hm; simp at hm
    | some x =>
        cases h2 : entry.geoIndex with
        | none => rw [h1, h2] at hm; simp at hm
        | some y => exact ⟨x, y, rfl, rfl⟩
  obtain ⟨k, hl⟩ : ∃ k, entry.blockLayout = some k := by
    cases h : entry.blockLayout with
    | some k => exact ⟨k, rfl⟩
    | none => have hm := andR (andL hv); rw [h] at hm; simp at hm
  have hq := andR hv
  have hgadm : entry.graphSet.all graphNameAdmitted := andR (andL (andR hq))
  have hMc : encodableChunked c := by
    have hm := andR (andL (andL (andL (andL (andL he))))); rw [hchunk] at hm; exact hm
  have hpair := andR (andL (andL hv))
  rw [hli, hgi] at hpair
  have hLav : artifactValidFor 9 l := andL (andL (andL hpair))
  have hGav : artifactValidFor 9 g := andR (andL hpair)
  have hMpair := andR (andL he)
  rw [hli, hgi] at hMpair
  have hMl : encodableSidecar l := andL hMpair
  have hMg : encodableSidecar g := andR hMpair
  have hMbl : (fitsU32 entry.blankNodeScope.toUTF8.size && fitsU32 entry.graphSet.length &&
      entry.graphSet.all graphNameEncodable) = true := by
    have hm := andR he; rw [hl] at hm; exact hm
  simp only [encodeEntry, hchunk, hl, hli, hgi, decodeEntry, List.append_assoc]
  rw [decodeCommon_encodeCommon entry _ hp hk hb hd hr hord]
  simp only [bind, Option.bind]
  rw [dif_pos entry.predicate.property,
    chunked_roundTrip _ (by decide) entry c _ hchunk hav hMc]
  simp only [bind, Option.bind]
  rw [sidecar_roundTrip _ (by decide) l _ hLav hMl]
  simp only [bind, Option.bind]
  rw [sidecar_roundTrip _ (by decide) g _ hGav hMg]
  simp only [bind, Option.bind]
  rw [decodeQuadTail_encodeQuadTail k entry.blankNodeScope entry.graphSet _
    (andL (andL hMbl)) (andR (andL hMbl)) (andR hMbl) hgadm]
  simp only [bind, Option.bind, Option.some.injEq, Prod.mk.injEq, and_true]
  exact entry_rebuild entry (some c) none none none (some l) (some g) (some k)
    entry.blankNodeScope entry.graphSet [] none none hchunk hs ht hoi hli hgi hl rfl rfl
    hbr hsz hoz entry.predicate.property


/-- SBM10 is SBM9 plus the blob-reference list and the two zone maps, written
    after the GBI1 sidecar and before the quad tail. -/
theorem decodeEntry_encodeEntry_quadZone (entry : Entry) (rest : List UInt8)
    (hv : entryValid 10 entry) (he : encodableEntry 10 entry) :
    decodeEntry 10 (encodeEntry 10 entry ++ rest) = some (entry, rest) := by
  obtain ⟨hp, hk, hb, hr, hord, hd⟩ := encodableEntry_common 10 entry he
  have hz := andR hv
  have hze := andR he
  have hv := andL hv
  have he := andL he
  have hav : artifactValidFor 10 entry.artifact :=
    andR (andL (andL (andL (andL (andL (andL hv))))))
  obtain ⟨c, hchunk⟩ : ∃ c, entry.artifact.chunked = some c := by
    cases h : entry.artifact.chunked with
    | some c => exact ⟨c, rfl⟩
    | none => have hm := andR hav; rw [h] at hm; simp at hm
  have hs : entry.subjectIndex = none := by
    cases h : entry.subjectIndex with
    | none => rfl
    | some x => have hm := andR (andL (andL (andL (andL (andL hv))))); rw [h] at hm; simp at hm
  have ht : entry.termIndex = none := by
    cases h : entry.termIndex with
    | none => rfl
    | some x => have hm := andR (andL (andL (andL (andL hv)))); rw [h] at hm; simp at hm
  have hoi : entry.objectIndex = none := by
    cases h : entry.objectIndex with
    | none => rfl
    | some x => have hm := andR (andL (andL (andL hv))); rw [h] at hm; simp at hm
  obtain ⟨l, g, hli, hgi⟩ :
      ∃ l g, entry.literalIndex = some l ∧ entry.geoIndex = some g := by
    have hm := andR (andL (andL hv))
    cases h1 : entry.literalIndex with
    | none =>
        cases h2 : entry.geoIndex with
        | none => rw [h1, h2] at hm; simp at hm
        | some y => rw [h1, h2] at hm; simp at hm
    | some x =>
        cases h2 : entry.geoIndex with
        | none => rw [h1, h2] at hm; simp at hm
        | some y => exact ⟨x, y, rfl, rfl⟩
  obtain ⟨k, hl⟩ : ∃ k, entry.blockLayout = some k := by
    cases h : entry.blockLayout with
    | some k => exact ⟨k, rfl⟩
    | none => have hm := andR (andL hv); rw [h] at hm; simp at hm
  have hq := andR hv
  have hgadm : entry.graphSet.all graphNameAdmitted := andR (andL (andR hq))
  have hMc : encodableChunked c := by
    have hm := andR (andL (andL (andL (andL (andL he))))); rw [hchunk] at hm; exact hm
  have hpair := andR (andL (andL hv))
  rw [hli, hgi] at hpair
  have hLav : artifactValidFor 10 l := andL (andL (andL hpair))
  have hGav : artifactValidFor 10 g := andR (andL hpair)
  have hMpair := andR (andL he)
  rw [hli, hgi] at hMpair
  have hMl : encodableSidecar l := andL hMpair
  have hMg : encodableSidecar g := andR hMpair
  have hMbl : (fitsU32 entry.blankNodeScope.toUTF8.size && fitsU32 entry.graphSet.length &&
      entry.graphSet.all graphNameEncodable) = true := by
    have hm := andR he; rw [hl] at hm; exact hm
  -- The SBM10 conjuncts: the blob references and the two zone maps.
  rw [sbm10EntryFields, if_pos (by decide)] at hz
  rw [sbm10EntryEncodable, if_pos (by decide)] at hze
  obtain ⟨sz, oz, hsz, hoz⟩ :
      ∃ sz oz, entry.subjectZone = some sz ∧ entry.objectZone = some oz := by
    have hm := andR hz
    cases h1 : entry.subjectZone with
    | none =>
        cases h2 : entry.objectZone with
        | none => rw [h1, h2] at hm; simp at hm
        | some y => rw [h1, h2] at hm; simp at hm
    | some x =>
        cases h2 : entry.objectZone with
        | none => rw [h1, h2] at hm; simp at hm
        | some y => exact ⟨x, y, rfl, rfl⟩
  have hzones := andR hz
  rw [hsz, hoz] at hzones
  have hszAdm : zoneAdmitted sz := andL hzones
  have hozAdm : zoneAdmitted oz := andR hzones
  have hszLo : fitsU32 sz.1.length :=
    fitsU32_of_le_zoneBytes (by simpa using andL (andL hszAdm))
  have hszHi : fitsU32 sz.2.length :=
    fitsU32_of_le_zoneBytes (by simpa using andR (andL hszAdm))
  have hozLo : fitsU32 oz.1.length :=
    fitsU32_of_le_zoneBytes (by simpa using andL (andL hozAdm))
  have hozHi : fitsU32 oz.2.length :=
    fitsU32_of_le_zoneBytes (by simpa using andR (andL hozAdm))
  simp only [encodeEntry, hchunk, hl, hli, hgi, hsz, hoz, decodeEntry, List.append_assoc]
  rw [decodeCommon_encodeCommon entry _ hp hk hb hd hr hord]
  simp only [bind, Option.bind]
  rw [dif_pos entry.predicate.property,
    chunked_roundTrip _ (by decide) entry c _ hchunk hav hMc]
  simp only [bind, Option.bind]
  rw [sidecar_roundTrip _ (by decide) l _ hLav hMl]
  simp only [bind, Option.bind]
  rw [sidecar_roundTrip _ (by decide) g _ hGav hMg]
  simp only [bind, Option.bind]
  rw [decodeBlobRefs_encodeBlobRefs entry.blobRefs _ (andL hze) (andR hze)]
  simp only [bind, Option.bind]
  rw [decodeZone_encodeZone sz _ hszLo hszHi]
  simp only [bind, Option.bind]
  rw [decodeZone_encodeZone oz _ hozLo hozHi]
  simp only [bind, Option.bind]
  rw [decodeQuadTail_encodeQuadTail k entry.blankNodeScope entry.graphSet _
    (andL (andL hMbl)) (andR (andL hMbl)) (andR hMbl) hgadm]
  simp only [bind, Option.bind, Option.some.injEq, Prod.mk.injEq, and_true]
  exact entry_rebuild entry (some c) none none none (some l) (some g) (some k)
    entry.blankNodeScope entry.graphSet entry.blobRefs (some sz) (some oz) hchunk hs ht hoi hli
    hgi hl rfl rfl rfl hsz hoz entry.predicate.property

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
  | 8 => exact decodeEntry_encodeEntry_quadLiteral entry rest hv he
  | 9 => exact decodeEntry_encodeEntry_quadGeo entry rest hv he
  | 10 => exact decodeEntry_encodeEntry_quadZone entry rest hv he
  | n + 11 =>
      exact absurd
        (andR (andR (andL (andL (andL (andL (andL (andL (andL hv))))))))) (by simp)

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

Only the eleven admitted versions are written, so the decoder's rejection test
is false and its `toNat` is exact. Both are decided one version at a time,
here, so the manifest proof itself does not split. -/

theorem versionByte_toNat (v : Nat) (h : v ≤ 10) : (UInt8.ofNat v).toNat = v := by
  match v, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ => decide
  | (n + 11), h => exact absurd h (by omega)

theorem versionByte_admitted (v : Nat) (h : v ≤ 10) :
    (UInt8.ofNat v != wireVersion0 && UInt8.ofNat v != wireVersion1 &&
      UInt8.ofNat v != wireVersion2 && UInt8.ofNat v != wireVersion3 &&
      UInt8.ofNat v != wireVersion4 && UInt8.ofNat v != wireVersion5 &&
      UInt8.ofNat v != wireVersion6 && UInt8.ofNat v != wireVersion7 &&
      UInt8.ofNat v != wireVersion8 && UInt8.ofNat v != wireVersion9 &&
      UInt8.ofNat v != wireVersion10) = false := by
  match v, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ => decide
  | (n + 11), h => exact absurd h (by omega)

/-- SBM7 through SBM10 all carry the publication profile, and no earlier
    version does, so the decoder's profile test is exactly this disjunction. -/
theorem versionByte_is7to10 (v : Nat) (h : v ≤ 10) :
    (UInt8.ofNat v == wireVersion7 || UInt8.ofNat v == wireVersion8 ||
      UInt8.ofNat v == wireVersion9 || UInt8.ofNat v == wireVersion10) =
      (v == 7 || v == 8 || v == 9 || v == 10) := by
  match v, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ => decide
  | (n + 11), h => exact absurd h (by omega)

/-- Only SBM10 carries the blob table. -/
theorem versionByte_is10 (v : Nat) (h : v ≤ 10) :
    (UInt8.ofNat v == wireVersion10) = (v == 10) := by
  match v, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ => decide
  | (n + 11), h => exact absurd h (by omega)

theorem decode?_encode? (manifest : Manifest) (bytes : ByteArray)
    (h : encode? manifest = some bytes) : decode? bytes = some manifest := by
  by_cases hgate : (valid manifest && encodable manifest) = true
  case neg => rw [encode?, if_neg hgate] at h; simp at h
  rw [encode?, if_pos hgate] at h
  have hvalid : valid manifest := andL hgate
  have hencodableAll : encodable manifest := andR hgate
  -- `valid` and `encodable` each gained ONE appended SBM10 conjunct, so every
  -- accessor chain below reads the base conjunction and the SBM10 facts are
  -- read from the appended one.
  have hvalidBase := andL hvalid
  have hencodable := andL hencodableAll
  have hverLe : manifest.version ≤ 10 := by
    have hv := andL (andL (andL (andL (andL (andL (andL hvalidBase))))))
    simp only [Bool.or_eq_true, beq_iff_eq] at hv
    omega
  have hsid : fitsU32 manifest.sourceIdentity.size := andL (andL (andL (andL (andL hencodable))))
  have htrv : fitsU32 manifest.termRegistryVersion.toUTF8.size :=
    andR (andL (andL (andL (andL hencodable))))
  have hlay : fitsU32 manifest.layout.toUTF8.size := andR (andL (andL (andL hencodable)))
  have hprof : fitsU32 manifest.blankNodeProfile.toUTF8.size := andR (andL (andL hencodable))
  have hcount : fitsU32 manifest.entries.length := andR (andL hencodable)
  have hentriesEnc : manifest.entries.all (encodableEntry manifest.version) := andR hencodable
  have hentriesVal : manifest.entries.all (entryValid manifest.version) := andR hvalidBase
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
    versionByte_is7to10 _ hverLe]
  -- Applied AFTER the four-fold profile test above, so that its own rewrite of
  -- the tenth version byte does not break that test's pattern.
  simp only [versionByte_is10 _ hverLe]
  rw [takeExact_of_length manifest.sourceIdentity.toList _ _
    (by rw [length_toList, u32_toNat_ofNat_of_lt hsl2])]
  simp only [bind, Option.bind]
  rw [decodeString_encodeString _ _ htrv]
  simp only [bind, Option.bind]
  rw [decodeString_encodeString _ _ hlay]
  simp only [bind, Option.bind]
  by_cases h10 : manifest.version = 10
  · -- SBM10: the profile is written, and the blob table follows the entries.
    have hprofile : (manifest.version == 7 || manifest.version == 8 ||
        manifest.version == 9 || manifest.version == 10) = true := by simp [h10]
    have hisBlob : (manifest.version == 10) = true := by simp [h10]
    have hblobFields : sbm10ManifestFields manifest := andR hvalid
    rw [sbm10ManifestFields, if_pos hisBlob] at hblobFields
    have hblobEncodable : sbm10ManifestEncodable manifest := andR hencodableAll
    rw [sbm10ManifestEncodable, if_pos hisBlob] at hblobEncodable
    have hblobValid : manifest.blobs.all (artifactValidFor 10) = true := by
      have hall := andL (andL (andL hblobFields))
      simp only [List.all_eq_true] at hall ⊢
      intro blob hmem
      exact andL (hall blob hmem)
    have hblobCount : fitsU32 manifest.blobs.length := andL hblobEncodable
    have hblobEnc : manifest.blobs.all encodableSidecar = true := andR hblobEncodable
    simp only [hprofile, if_true]
    simp only [hisBlob, if_true]
    rw [decodeString_encodeString _ _ hprof]
    simp only [bind, Option.bind, readU32LE_writeU32LE_append,
      u32_toNat_ofNat_of_lt hn, drop4_writeU32LE]
    rw [decodeEntries_flatMap _ manifest.entries _ hentriesVal hentriesEnc]
    simp only [bind, Option.bind]
    rw [show encodeBlobTable manifest.blobs = encodeBlobTable manifest.blobs ++ [] by simp,
      decodeBlobTable_encodeBlobTable manifest.blobs [] hblobCount hblobValid hblobEnc]
    simp only [bind, Option.bind, List.isEmpty_nil, Bool.true_and, byteArrayOfList_toList]
    simp only [hvalid, if_true]
  · have hnot10 : (manifest.version == 10) = false := by simp [h10]
    simp only [hnot10, Bool.false_eq_true, if_false, List.append_nil, Bool.or_false]
    have hblobsEmpty : manifest.blobs = [] := by
      have hf : sbm10ManifestFields manifest := andR hvalid
      rw [sbm10ManifestFields, if_neg (by simp [hnot10])] at hf
      simpa using hf
    by_cases h7 : manifest.version = 7 ∨ manifest.version = 8 ∨ manifest.version = 9
    · have hprofile : (manifest.version == 7 || manifest.version == 8 ||
          manifest.version == 9) = true := by
        rcases h7 with h | h | h <;> simp [h]
      simp only [hprofile, if_true]
      rw [decodeString_encodeString _ _ hprof]
      simp only [bind, Option.bind, readU32LE_writeU32LE_append,
        u32_toNat_ofNat_of_lt hn, drop4_writeU32LE]
      rw [decodeEntries_flatMap_nil _ manifest.entries hentriesVal hentriesEnc]
      simp only [bind, Option.bind, List.isEmpty_nil, Bool.true_and, byteArrayOfList_toList,
        ← hblobsEmpty]
      simp only [hvalid, if_true]
    · have h7' := not_or.mp h7
      have h89 := not_or.mp h7'.2
      have hprofEmpty : manifest.blankNodeProfile = "" := by
        have hq := andR (andL (andL (andL (andL (andL hvalidBase)))))
        rw [if_neg (by simp [h7'.1, h89.1, h89.2, h10])] at hq
        simpa using hq
      simp only [show (manifest.version == 7 || manifest.version == 8 ||
          manifest.version == 9) = false from by
          simp [h7'.1, h89.1, h89.2], Bool.false_eq_true,
        if_false, List.nil_append, bind, Option.bind, readU32LE_writeU32LE_append,
        u32_toNat_ofNat_of_lt hn, drop4_writeU32LE]
      rw [decodeEntries_flatMap_nil _ manifest.entries hentriesVal hentriesEnc]
      simp only [bind, Option.bind, List.isEmpty_nil, Bool.true_and, byteArrayOfList_toList,
        ← hprofEmpty, ← hblobsEmpty]
      simp only [hvalid, if_true]

#print axioms decodeString_encodeString
#print axioms decodeGraphNames_flatMap
#print axioms decodeEntry_encodeEntry
#print axioms decodeEntries_flatMap
#print axioms lexLe_take
#print axioms zoneMap_sound
#print axioms decodeBlobTable_encodeBlobTable
#print axioms decode?_encode?

end L4Factoidal.Storage.ShardManifest
