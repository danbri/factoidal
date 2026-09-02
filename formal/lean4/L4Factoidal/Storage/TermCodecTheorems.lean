/-
L4Factoidal.Storage.TermCodecTheorems — round-trip proofs for the durable
term codec of `L4Factoidal.Storage.DeltaLog`.

The delta log and the `BLK0` block wire format both encode an RDF term
with `serializeTerm?` and decode it with `parseTerm`. This module proves
that the decoder inverts the encoder on the subset the encoder admits,
with arbitrary trailing bytes present:

    serializeTerm? t = some bs → parseTerm (bs ++ rest) = some (t, rest)

The trailing-bytes form is what a framed reader needs. A record decoder
calls `parseTerm` on the remainder of a buffer, not on a byte sequence
that stops at the end of the term.

The proofs are layered. `stringOfBytes?_bytesOfString` is the UTF-8
round trip for one string. `parseLString_serializeLString?` lifts it to
the u32 length-prefixed field, over the little-endian field lemmas of
`L4Factoidal.Storage.Bytes`. `parseTerm_serializeTerm?` then follows the
tag dispatch of `parseTerm` case by case.

The literal case carries a hypothesis. `serializeTerm?` writes a
language tag but never a base direction, so a literal with
`direction = some _` does not round-trip; `parseTerm` refuses it,
because `literalWf` rejects a language tag with `rdf:dirLangString` and
no direction. The admitted subset is
`L4Factoidal.Storage.BlockWireV0.termSupported`, which is the predicate
the block encoder already gates on.

`termFitsU32` is the second admission condition: every length-prefixed
string in the term has a byte length below the u32 field limit.
Together the two conditions make the total encoder `serializeTerm` agree
with `serializeTerm?`, which gives the round trip in the form the block
codecs use.

`termFitsU32b_iff` relates `termFitsU32` to the decision procedure
`L4Factoidal.Storage.termFitsU32b` of `DeltaLog`. The block encoders gate
on that `Bool`, so both admission conditions are consequences of an
encoder's own guard and neither is a hypothesis of a codec round trip.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.DeltaLog
import L4Factoidal.Storage.BlockWireV0

namespace L4Factoidal.Storage

open L4Factoidal.RDF

/-! ## `ByteArray.toList`

`ByteArray.toList` is defined by an index loop rather than by
`data.toList`, and core carries no lemma relating the two. The UTF-8
round trip below needs that relation, because `bytesOfString` goes
through `ByteArray.toList` and `stringOfBytes?` rebuilds a `ByteArray`
from the list. -/

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

/-- The index loop of `ByteArray.toList` yields the underlying array's
element list. -/
private theorem byteArray_toList_eq (bs : ByteArray) : bs.toList = bs.data.toList := by
  rw [ByteArray.toList, byteArray_toList_loop]; simp

/-! ## Length-prefixed strings -/

/-- The UTF-8 byte list of a string decodes back to that string. -/
theorem stringOfBytes?_bytesOfString (s : String) :
    stringOfBytes? (bytesOfString s) = some s := by
  rw [stringOfBytes?, bytesOfString, byteArray_toList_eq, Array.toArray_toList]
  simp [String.fromUTF8?, s.isValidUTF8, String.fromUTF8]

/-- A four-byte little-endian field is exactly what a reader steps over. -/
private theorem drop4_writeU32LE (n : UInt32) (t : List UInt8) :
    (writeU32LE n ++ t).drop 4 = t := by simp [writeU32LE]

/-- The length-prefixed string decoder inverts the admission-preserving
encoder and returns the trailing bytes unchanged. -/
theorem parseLString_serializeLString? (s : String) (bs rest : List UInt8)
    (h : serializeLString? s = some bs) :
    parseLString (bs ++ rest) = some (s, rest) := by
  by_cases hge : (bytesOfString s).length ≥ UInt32.size
  · rw [serializeLString?] at h; simp [hge] at h
  · rw [serializeLString?] at h
    simp only [hge, if_false, Option.some.injEq] at h
    subst h
    have hlt : (bytesOfString s).length < UInt32.size := Nat.lt_of_not_le hge
    rw [List.append_assoc, parseLString, readU32LE_writeU32LE_append]
    simp only [u32_toNat_ofNat_of_lt hlt, drop4_writeU32LE, List.take_left,
      List.drop_left, bne_self_eq_false, Bool.false_eq_true, if_false,
      stringOfBytes?_bytesOfString, Option.map_some]

/-- The single-byte decoder consumes exactly the head byte. -/
theorem parseU8_cons (b : UInt8) (rest : List UInt8) :
    parseU8 (b :: rest) = some (b, rest) := rfl

/-! ## Subjects -/

/-- The subject decoder inverts the admission-preserving subject encoder
and returns the trailing bytes unchanged. -/
theorem parseSubject_serializeSubject? (s : Subject) (bs rest : List UInt8)
    (h : serializeSubject? s = some bs) :
    parseSubject (bs ++ rest) = some (s, rest) := by
  cases s with
  | iri i =>
      rw [serializeSubject?, Option.map_eq_some_iff] at h
      obtain ⟨sb, hsb, rfl⟩ := h
      rw [List.cons_append, parseSubject]
      simp [parseU8, subjTagIri, parseLString_serializeLString? _ _ _ hsb, i.property]
  | bnode b =>
      rw [serializeSubject?, Option.map_eq_some_iff] at h
      obtain ⟨sb, hsb, rfl⟩ := h
      rw [List.cons_append, parseSubject]
      simp [parseU8, subjTagIri, subjTagBnode, parseLString_serializeLString? _ _ _ hsb]

/-! ## Terms

`DeltaLog.mkLiteral?` — the literal reconstruction step of `parseTerm` —
is `private`, so it cannot be named here. `mkLiteralLocal` is a
definitionally equal copy; `show` bridges the two where `parseTerm`
unfolds. -/

private def mkLiteralLocal (lex dt : String) (tag : Option String) : Option Term :=
  if h : isIri dt then
    let l : Literal := { lexicalForm := lex, datatype := ⟨dt, h⟩,
                         langTag := tag, direction := none }
    if hw : literalWf l then some (.literal ⟨l, hw⟩) else none
  else none

/-- Reconstruction from lexical form, datatype IRI and language tag
returns the original literal when its base direction is absent. -/
private theorem mkLiteralLocal_self (l : WfLiteral) (hd : l.val.direction = none) :
    mkLiteralLocal l.val.lexicalForm l.val.datatype.val l.val.langTag
      = some (.literal l) := by
  rw [mkLiteralLocal, dif_pos l.val.datatype.property]
  have hrec : ({ lexicalForm := l.val.lexicalForm,
                 datatype := ⟨l.val.datatype.val, l.val.datatype.property⟩,
                 langTag := l.val.langTag, direction := none } : Literal) = l.val := by
    rw [← hd]
  simp only [hrec]
  rw [dif_pos l.property]

/-- The literal case of the term round trip, kept separate because it
splits on the language tag. -/
private theorem parseTerm_serializeTerm?_literal (l : WfLiteral) (bs rest : List UInt8)
    (hd : l.val.direction = none) (h : serializeTerm? (.literal l) = some bs) :
    parseTerm (bs ++ rest) = some (.literal l, rest) := by
  rw [serializeTerm?] at h
  cases hlex : serializeLString? l.val.lexicalForm with
  | none => rw [hlex] at h; simp [bind, Option.bind] at h
  | some lexb =>
  cases hdt : serializeLString? l.val.datatype.val with
  | none => rw [hlex, hdt] at h; simp [bind, Option.bind] at h
  | some dtb =>
  rw [hlex, hdt] at h
  simp only [bind, Option.bind] at h
  cases hlt : l.val.langTag with
  | none =>
      rw [hlt] at h
      simp only [Option.some.injEq] at h
      subst h
      have h1 := parseLString_serializeLString? l.val.lexicalForm lexb
        (dtb ++ (0 : UInt8) :: rest) hlex
      have h2 := parseLString_serializeLString? l.val.datatype.val dtb
        ((0 : UInt8) :: rest) hdt
      have happ : lexb ++ dtb ++ [(0 : UInt8)] ++ rest
          = lexb ++ (dtb ++ (0 : UInt8) :: rest) := by
        simp [List.append_assoc]
      rw [List.cons_append, happ, parseTerm]
      simp only [bind, Option.bind, parseU8, h1, h2, termTagIri, termTagBnode,
        termTagLiteral]
      rw [if_neg (by decide), if_neg (by decide), if_pos (by decide),
        if_pos (by decide)]
      have hmk := mkLiteralLocal_self l hd
      rw [hlt] at hmk
      show Option.map (fun t => (t, rest))
        (mkLiteralLocal l.val.lexicalForm l.val.datatype.val none)
          = some (Term.literal l, rest)
      rw [hmk]
      rfl
  | some tag =>
      rw [hlt] at h
      dsimp only at h
      cases hlang : serializeLString? tag with
      | none => rw [hlang] at h; simp at h
      | some langb =>
      rw [hlang] at h
      simp only [Option.some.injEq] at h
      subst h
      have h1 := parseLString_serializeLString? l.val.lexicalForm lexb
        (dtb ++ (1 : UInt8) :: (langb ++ rest)) hlex
      have h2 := parseLString_serializeLString? l.val.datatype.val dtb
        ((1 : UInt8) :: (langb ++ rest)) hdt
      have h3 := parseLString_serializeLString? tag langb rest hlang
      have happ : lexb ++ dtb ++ (1 : UInt8) :: langb ++ rest
          = lexb ++ (dtb ++ (1 : UInt8) :: (langb ++ rest)) := by
        simp [List.append_assoc]
      rw [List.cons_append, happ, parseTerm]
      simp only [bind, Option.bind, parseU8, h1, h2, h3, termTagIri, termTagBnode,
        termTagLiteral]
      rw [if_neg (by decide), if_neg (by decide), if_pos (by decide),
        if_neg (by decide), if_pos (by decide)]
      have hmk := mkLiteralLocal_self l hd
      rw [hlt] at hmk
      show Option.map (fun t => (t, rest))
        (mkLiteralLocal l.val.lexicalForm l.val.datatype.val (some tag))
          = some (Term.literal l, rest)
      rw [hmk]
      rfl

/-- The term decoder inverts the admission-preserving term encoder on
the subset `BlockWireV0.termSupported` admits, and returns the trailing
bytes unchanged.

The support hypothesis is needed only for the literal case: a literal
with a base direction serialises its language tag without the direction,
and `parseTerm` then refuses the record. -/
theorem parseTerm_serializeTerm? (t : Term) (bs rest : List UInt8)
    (hsup : BlockWireV0.termSupported t = true)
    (h : serializeTerm? t = some bs) :
    parseTerm (bs ++ rest) = some (t, rest) := by
  cases t with
  | iri i =>
      rw [serializeTerm?, Option.map_eq_some_iff] at h
      obtain ⟨sb, hsb, rfl⟩ := h
      rw [List.cons_append, parseTerm]
      simp [parseU8, termTagIri, parseLString_serializeLString? _ _ _ hsb, i.property]
  | bnode b =>
      rw [serializeTerm?, Option.map_eq_some_iff] at h
      obtain ⟨sb, hsb, rfl⟩ := h
      rw [List.cons_append, parseTerm]
      simp [parseU8, termTagIri, termTagBnode,
        parseLString_serializeLString? _ _ _ hsb]
  | literal l =>
      rw [BlockWireV0.termSupported, Option.isNone_iff_eq_none] at hsup
      exact parseTerm_serializeTerm?_literal l bs rest hsup h
  | tripleTerm s p o =>
      rw [serializeTerm?] at h
      exact absurd h (by simp)

/-! ## The total encoder

`serializeTerm` is the total encoder the block codecs call.
`serializeTerm?` is the same bytes plus an admission check, so the two
agree exactly when the term is supported and every length-prefixed
string in it fits the u32 field. -/

/-- A string whose UTF-8 byte length fits the u32 length prefix. -/
def stringFitsU32 (s : String) : Prop := (bytesOfString s).length < UInt32.size

/-- Every length-prefixed string in the term fits its u32 length prefix.
A triple term has no encoding at all, so it never fits. -/
def termFitsU32 : Term → Prop
  | .iri i => stringFitsU32 i.val
  | .bnode b => stringFitsU32 b
  | .literal l =>
      stringFitsU32 l.val.lexicalForm ∧ stringFitsU32 l.val.datatype.val ∧
        ∀ tag, l.val.langTag = some tag → stringFitsU32 tag
  | .tripleTerm _ _ _ => False

/-- The decision procedure `stringFitsU32b` of `L4Factoidal.Storage.DeltaLog`
decides `stringFitsU32`. -/
theorem stringFitsU32b_iff (s : String) : stringFitsU32b s = true ↔ stringFitsU32 s := by
  simp [stringFitsU32b, stringFitsU32]

/-- The decision procedure `termFitsU32b` of `L4Factoidal.Storage.DeltaLog`
decides `termFitsU32`. This is what lets a block encoder gate on the u32
length-prefix condition with a `Bool` guard and a proof read the `Prop` out
of that guard. -/
theorem termFitsU32b_iff (t : Term) : termFitsU32b t = true ↔ termFitsU32 t := by
  cases t with
  | iri i => exact stringFitsU32b_iff i.val
  | bnode b => exact stringFitsU32b_iff b
  | literal l =>
      rw [termFitsU32b, termFitsU32, Bool.and_eq_true, Bool.and_eq_true,
        stringFitsU32b_iff, stringFitsU32b_iff]
      constructor
      · rintro ⟨⟨hlex, hdt⟩, htag⟩
        refine ⟨hlex, hdt, ?_⟩
        intro tag htageq
        simp only [htageq] at htag
        exact (stringFitsU32b_iff tag).mp htag
      · rintro ⟨hlex, hdt, htag⟩
        refine ⟨⟨hlex, hdt⟩, ?_⟩
        cases hlt : l.val.langTag with
        | none => rfl
        | some tag => exact (stringFitsU32b_iff tag).mpr (htag tag hlt)
  | tripleTerm s p o => simp [termFitsU32b, termFitsU32]

/-- The admission-preserving string encoder emits the total encoder's
bytes whenever the byte length fits. -/
theorem serializeLString?_eq_some (s : String) (h : stringFitsU32 s) :
    serializeLString? s = some (serializeLString s) := by
  rw [serializeLString?, serializeLString]
  exact if_neg (Nat.not_le.2 h)

/-- On the supported, fitting subset the admission-preserving term
encoder emits exactly the total encoder's bytes. -/
theorem serializeTerm?_eq_some_of_fits (t : Term) (hfit : termFitsU32 t) :
    serializeTerm? t = some (serializeTerm t) := by
  cases t with
  | iri i =>
      rw [serializeTerm?, serializeTerm, serializeLString?_eq_some _ hfit]
      rfl
  | bnode b =>
      rw [serializeTerm?, serializeTerm, serializeLString?_eq_some _ hfit]
      rfl
  | literal l =>
      obtain ⟨hlex, hdt, htag⟩ := hfit
      rw [serializeTerm?, serializeTerm, serializeLString?_eq_some _ hlex,
        serializeLString?_eq_some _ hdt]
      simp only [bind, Option.bind]
      cases hlt : l.val.langTag with
      | none => rfl
      | some tag =>
          dsimp only
          rw [serializeLString?_eq_some _ (htag tag hlt)]
  | tripleTerm s p o => exact absurd hfit (by simp [termFitsU32])

/-- The round trip in the form the block codecs use: the total encoder's
bytes, followed by arbitrary trailing bytes, decode back to the term. -/
theorem parseTerm_serializeTerm (t : Term) (rest : List UInt8)
    (hsup : BlockWireV0.termSupported t = true) (hfit : termFitsU32 t) :
    parseTerm (serializeTerm t ++ rest) = some (t, rest) :=
  parseTerm_serializeTerm? t (serializeTerm t) rest hsup
    (serializeTerm?_eq_some_of_fits t hfit)

#print axioms stringOfBytes?_bytesOfString
#print axioms parseLString_serializeLString?
#print axioms parseU8_cons
#print axioms parseSubject_serializeSubject?
#print axioms parseTerm_serializeTerm?
#print axioms termFitsU32b_iff
#print axioms serializeTerm?_eq_some_of_fits
#print axioms parseTerm_serializeTerm

end L4Factoidal.Storage
