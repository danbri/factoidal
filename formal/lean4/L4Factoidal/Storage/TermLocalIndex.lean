/-
L4Factoidal.Storage.TermLocalIndex — pure term-to-local-ID lookup meaning.

This is the semantic core for the future TLI1 companion object. IBK3 local
TermIds are never used as global RDF identities: a lookup begins with an RDF
term and returns an ID only after complete structural equality confirms the
matching dictionary entry. The eventual wire format will page these canonical
entries; this module deliberately fixes their order and lookup result first.
-/
import L4Factoidal.Storage.PagedTermDictionary

namespace L4Factoidal.Storage.TermLocalIndex

open L4Factoidal.RDF
open L4Factoidal.Storage.BlockWireV0
open L4Factoidal.Storage.PagedTermDictionary

structure Entry where
  /-- Existing canonical RDF term bytes, retained so a wire index does not
      define a rival spelling of RDF terms. -/
  key : List UInt8
  term : Term
  localId : Nat
  deriving DecidableEq, Repr

/-- The canonical key order, stated over the stored `List UInt8` key. This
    remains the specification of the entry order; `lessBytesBytes` below is the
    form the build actually runs, and `lessBytesBytes_ofKey` proves the two
    agree. -/
private def lessBytes : List UInt8 → List UInt8 → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | left :: leftRest, right :: rightRest =>
      if left < right then true
      else if left == right then lessBytes leftRest rightRest
      else false

private def before (left right : Entry) : Bool :=
  lessBytes left.key right.key

/-- The same key bytes as one `ByteArray`. Sorting a whole dictionary walked
    one cons cell per compared byte; the packed form is compared by index. -/
def keyBytes (key : List UInt8) : ByteArray := ByteArray.mk key.toArray

/-- Index loop for the canonical key order. `fuel` is one more than the number
    of positions the loop can compare, so its exhausted case is unreachable;
    `lessBytesGo_eq` carries that condition as a hypothesis. -/
private def lessBytesGo (left right : ByteArray) (index : Nat) : Nat -> Bool
  | 0 => false
  | fuel + 1 =>
      if hleft : index < left.size then
        if hright : index < right.size then
          (if left[index] < right[index] then true
           else if left[index] == right[index] then lessBytesGo left right (index + 1) fuel
           else false)
        else false
      else if index < right.size then true else false

/-- The canonical key order on packed keys. -/
def lessBytesBytes (left right : ByteArray) : Bool :=
  lessBytesGo left right 0 (min left.size right.size + 1)

private theorem length_dataToList (bytes : ByteArray) :
    bytes.data.toList.length = bytes.size := rfl

private theorem getElem_dataToList (bytes : ByteArray) (index : Nat)
    (hsize : index < bytes.size) :
    bytes.data.toList[index]'(by rw [length_dataToList]; exact hsize) = bytes[index] := by
  simp [ByteArray.getElem_eq_getElem_data]

private theorem lessBytesGo_eq :
    forall (fuel : Nat) (left right : ByteArray) (index : Nat),
      index <= min left.size right.size ->
      index + fuel = min left.size right.size + 1 ->
      lessBytesGo left right index fuel
        = lessBytes (left.data.toList.drop index) (right.data.toList.drop index) := by
  intro fuel
  induction fuel with
  | zero => intro left right index hle heq; exact absurd heq (by omega)
  | succ fuel ih =>
      intro left right index hle heq
      have hlenLeft : left.data.toList.length = left.size := length_dataToList left
      have hlenRight : right.data.toList.length = right.size := length_dataToList right
      unfold lessBytesGo
      by_cases hleft : index < left.size
      · by_cases hright : index < right.size
        · have hL : index < left.data.toList.length := by omega
          have hR : index < right.data.toList.length := by omega
          rw [List.drop_eq_getElem_cons hL, List.drop_eq_getElem_cons hR,
            getElem_dataToList left index hleft, getElem_dataToList right index hright,
            dif_pos hleft, dif_pos hright]
          simp only [lessBytes]
          by_cases hlt : left[index] < right[index]
          · simp [hlt]
          · by_cases heqByte : left[index] == right[index]
            · rw [if_neg hlt, if_neg hlt, if_pos heqByte, if_pos heqByte]
              exact ih left right (index + 1) (by omega) (by omega)
            · simp [hlt, heqByte]
        · have hL : index < left.data.toList.length := by omega
          have hnil : right.data.toList.drop index = [] :=
            List.drop_eq_nil_of_le (by omega)
          rw [List.drop_eq_getElem_cons hL, hnil, dif_pos hleft, dif_neg hright]
          simp [lessBytes]
      · by_cases hright : index < right.size
        · have hR : index < right.data.toList.length := by omega
          have hnil : left.data.toList.drop index = [] :=
            List.drop_eq_nil_of_le (by omega)
          rw [List.drop_eq_getElem_cons hR, hnil, dif_neg hleft, if_pos hright]
          simp [lessBytes]
        · have hnilLeft : left.data.toList.drop index = [] :=
            List.drop_eq_nil_of_le (by omega)
          have hnilRight : right.data.toList.drop index = [] :=
            List.drop_eq_nil_of_le (by omega)
          rw [hnilLeft, hnilRight, dif_neg hleft, if_neg hright]
          simp [lessBytes]

/-- The packed comparison is the canonical key order of the stored bytes. -/
theorem lessBytesBytes_eq (left right : ByteArray) :
    lessBytesBytes left right = lessBytes left.data.toList right.data.toList := by
  have := lessBytesGo_eq (min left.size right.size + 1) left right 0 (by omega) (by omega)
  simpa [lessBytesBytes] using this

/-- Packing a stored key and comparing by index decides exactly the canonical
    key order of the entry keys, so the entry order is unchanged. -/
theorem lessBytesBytes_ofKey (left right : List UInt8) :
    lessBytesBytes (keyBytes left) (keyBytes right) = lessBytes left right := by
  simpa [keyBytes] using lessBytesBytes_eq (keyBytes left) (keyBytes right)

private def entriesGo : Nat → List Term → List Entry
  | _, [] => []
  | localId, term :: rest =>
      { key := serializeTerm term, term, localId } :: entriesGo (localId + 1) rest

private def decorate (entry : Entry) : ByteArray × Entry := (keyBytes entry.key, entry)

private def beforeBytes (left right : ByteArray × Entry) : Bool :=
  lessBytesBytes left.1 right.1

/-- Canonical entries, lexicographically sorted by the established term
    serialization. IDs remain the original PTD1 dictionary positions.
    Each key is packed once and compared by index; `entriesOf_eq_spec` proves
    this is the `entriesOfSpec` order, which is stated over the stored
    `List UInt8` keys. -/
def entriesOf (terms : Array Term) : Array Entry :=
  (((entriesGo 0 terms.toList).toArray.map decorate).mergeSort beforeBytes).map Prod.snd

/-- The specification of `entriesOf`: the same entries sorted by the canonical
    key order of the stored keys. -/
def entriesOfSpec (terms : Array Term) : Array Entry :=
  (entriesGo 0 terms.toList).toArray.mergeSort before

theorem entriesOf_eq_spec (terms : Array Term) : entriesOf terms = entriesOfSpec terms := by
  have hcmp : ∀ a ∈ (entriesGo 0 terms.toList).toArray.map decorate,
      ∀ b ∈ (entriesGo 0 terms.toList).toArray.map decorate,
      beforeBytes a b = before (Prod.snd a) (Prod.snd b) := by
    intro a ha b hb
    simp only [Array.mem_map] at ha hb
    obtain ⟨x, _, rfl⟩ := ha
    obtain ⟨y, _, rfl⟩ := hb
    simpa [beforeBytes, before, decorate] using lessBytesBytes_ofKey x.key y.key
  unfold entriesOf entriesOfSpec
  rw [Array.map_mergeSort hcmp]
  congr 1
  simp [decorate, Function.comp_def]

private def lowerBoundGo (entries : Array Entry) (key : List UInt8) (low high : Nat) : Nat → Nat
  | 0 => low
  | fuel + 1 =>
      if low >= high then low
      else
        let middle := low + (high - low) / 2
        match entries[middle]? with
        | none => low
        | some entry =>
            if lessBytes entry.key key then
              lowerBoundGo entries key (middle + 1) high fuel
            else lowerBoundGo entries key low middle fuel

/-- Total canonical lookup. A byte-equal candidate is still checked as an RDF
    term; this remains correct if a future codec or host has a representation
    defect, and records the non-negotiable identity boundary for hash indexes.
    `none` means the term is absent, not that an untrusted local ID is zero. -/
def lookup? (entries : Array Entry) (wanted : Term) : Option Nat :=
  let key := serializeTerm wanted
  let index := lowerBoundGo entries key 0 entries.size (entries.size + 1)
  match entries[index]? with
  | some entry => if entry.key == key && entry.term == wanted then some entry.localId else none
  | none => none

/-- The direct dictionary lookup is the reference contract for a TLI1 decoder
    and range reader. -/
def agreesWithDictionary (terms : Array Term) (wanted : Term) : Bool :=
  lookup? (entriesOf terms) wanted == findTermId? terms wanted

private def ex : WfIri := ⟨"https://example.test/a", by decide⟩
private def ex2 : WfIri := ⟨"https://example.test/b", by decide⟩
private def sample : Array Term := #[.iri ex2, .bnode "b", .iri ex]

#guard lookup? (entriesOf sample) (.iri ex2) == some 0
#guard lookup? (entriesOf sample) (.bnode "b") == some 1
#guard lookup? (entriesOf sample) (.iri ex) == some 2
#guard lookup? (entriesOf sample) (.bnode "missing") == none
#guard agreesWithDictionary sample (.iri ex)
#guard agreesWithDictionary sample (.bnode "missing")
#guard entriesOf sample == entriesOfSpec sample

end L4Factoidal.Storage.TermLocalIndex
