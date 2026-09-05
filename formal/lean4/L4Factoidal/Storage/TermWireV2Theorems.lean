/-
L4Factoidal.Storage.TermWireV2Theorems — round-trip and resolution proofs
for term codec v2.

Two results.

    parseTerm_serializeTerm? : serializeTerm? w = some bs →
      parseTerm (bs ++ rest) = some (w, rest)

is the round trip in the form a framed reader needs: the decoder runs on
the remainder of a buffer, not on bytes that stop at the end of the term.
It carries no admission hypothesis, because `serializeTerm?` performs the
whole admission test itself and `parseTerm` tests exactly the same
conditions.

    resolve_toWire : resolve h (lookupOf h t) (toWire h t) = some t

is the packer's obligation: choosing the tag by lexical byte length and
then resolving through the literal's own bytes gives the term back, for
any hash function `h`.

`toWire_inline_iff` and `toWire_blob_iff` state the canonical rule of
section 4.1 as an equivalence on the lexical byte length.

The fuel of `parseInlineGo` is discharged by `tdepth_le_length`: every
nesting level of a triple term writes at least its own tag byte, so the
byte length of an encoding is at least the term's nesting depth, and
`parseInline` supplies the whole input length as fuel. The conclusion of
the round trip therefore mentions no fuel.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.TermWireV2
import L4Factoidal.Storage.TermCodecTheorems

namespace L4Factoidal.Storage.TermWireV2

open L4Factoidal.RDF
open L4Factoidal.Storage

/-! ## The language-tag and direction field -/

theorem parseLangField_serializeLangField? (langTag : Option String)
    (direction : Option TextDirection) (bs rest : List UInt8)
    (h : serializeLangField? langTag direction = some bs) :
    parseLangField (bs ++ rest) = some ((langTag, direction), rest) := by
  cases langTag with
  | none =>
      cases direction with
      | none =>
          rw [serializeLangField?] at h
          simp only [Option.some.injEq] at h
          subst h
          simp [parseLangField, parseU8]
      | some d => rw [serializeLangField?] at h; exact absurd h (by simp)
  | some t =>
      cases direction with
      | none =>
          rw [serializeLangField?, Option.map_eq_some_iff] at h
          obtain ⟨tb, htb, rfl⟩ := h
          rw [List.cons_append, parseLangField]
          simp [parseU8, parseLString_serializeLString? _ _ _ htb]
      | some d =>
          cases d with
          | ltr =>
              rw [serializeLangField?, Option.map_eq_some_iff] at h
              obtain ⟨tb, htb, rfl⟩ := h
              rw [List.cons_append, parseLangField]
              simp [parseU8, parseLString_serializeLString? _ _ _ htb]
          | rtl =>
              rw [serializeLangField?, Option.map_eq_some_iff] at h
              obtain ⟨tb, htb, rfl⟩ := h
              rw [List.cons_append, parseLangField]
              simp [parseU8, parseLString_serializeLString? _ _ _ htb]

/-! ## Literal reconstruction

`TermWireV2.mkLiteral?` is `private`, so a definitionally equal copy is
used here and `show` bridges the two where `parseInlineGo` unfolds. -/

private def mkLiteralLocal (lex dt : String) (langTag : Option String)
    (direction : Option TextDirection) : Option Term :=
  if h : isIri dt then
    let l : Literal := { lexicalForm := lex, datatype := ⟨dt, h⟩,
                         langTag := langTag, direction := direction }
    if hw : literalWf l then some (.literal ⟨l, hw⟩) else none
  else none

private theorem mkLiteralLocal_self (l : WfLiteral) :
    mkLiteralLocal l.val.lexicalForm l.val.datatype.val l.val.langTag
      l.val.direction = some (.literal l) := by
  rw [mkLiteralLocal, dif_pos l.val.datatype.property]
  have hrec : ({ lexicalForm := l.val.lexicalForm,
                 datatype := ⟨l.val.datatype.val, l.val.datatype.property⟩,
                 langTag := l.val.langTag,
                 direction := l.val.direction } : Literal) = l.val := rfl
  simp only [hrec]
  rw [dif_pos l.property]

/-! ## The fuel measure -/

/-- The nesting depth of a term: one per triple-term level, one for a
leaf. Every level writes at least its tag byte. -/
def tdepth : Term → Nat
  | .tripleTerm _ _ o => tdepth o + 1
  | _ => 1

/-- An inline encoding is at least as long as the term's nesting depth,
which is what makes the input length an adequate fuel. -/
theorem tdepth_le_length : ∀ (t : Term) (bs : List UInt8),
    serializeInline? t = some bs → tdepth t ≤ bs.length := by
  intro t
  induction t with
  | iri i =>
      intro bs h
      rw [serializeInline?, Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h
      simp [tdepth]
  | bnode b =>
      intro bs h
      rw [serializeInline?, Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h
      simp [tdepth]
  | literal l =>
      intro bs h
      rw [serializeInline?] at h
      by_cases hfit : lexicalFitsInline l
      · simp only [hfit, Bool.not_true, Bool.false_eq_true, if_false] at h
        cases hlex : serializeLString? l.val.lexicalForm with
        | none => rw [hlex] at h; simp at h
        | some lexb =>
        cases hdt : serializeLString? l.val.datatype.val with
        | none => rw [hlex, hdt] at h; simp at h
        | some dtb =>
        cases hlang : serializeLangField? l.val.langTag l.val.direction with
        | none => rw [hlex, hdt, hlang] at h; simp at h
        | some langb =>
        rw [hlex, hdt, hlang] at h
        simp only [bind, Option.bind, Option.some.injEq] at h
        subst h
        simp [tdepth]
      · simp only [hfit, Bool.not_false, if_true] at h
        exact absurd h (by simp)
  | tripleTerm s p o ih =>
      intro bs h
      rw [serializeInline?] at h
      cases hs : serializeSubject? s with
      | none => rw [hs] at h; simp at h
      | some sb =>
      cases hp : serializeLString? p.val with
      | none => rw [hs, hp] at h; simp at h
      | some pb =>
      cases ho : serializeInline? o with
      | none => rw [hs, hp, ho] at h; simp at h
      | some ob =>
      rw [hs, hp, ho] at h
      simp only [bind, Option.bind, Option.some.injEq] at h
      subst h
      have hdo := ih ob ho
      simp only [tdepth, List.length_cons, List.length_append]
      omega

/-! ## The inline round trip -/

/-- The inline decoder inverts the inline encoder for any fuel at or
above the term's nesting depth. -/
theorem parseInlineGo_serializeInline? : ∀ (t : Term) (fuel : Nat)
    (bs rest : List UInt8), tdepth t ≤ fuel → serializeInline? t = some bs →
    parseInlineGo fuel (bs ++ rest) = some (t, rest) := by
  intro t
  induction t with
  | iri i =>
      intro fuel bs rest hfuel h
      cases fuel with
      | zero => simp [tdepth] at hfuel
      | succ f =>
      rw [serializeInline?, Option.map_eq_some_iff] at h
      obtain ⟨sb, hsb, rfl⟩ := h
      rw [List.cons_append, parseInlineGo]
      simp [parseU8, tagIri, parseLString_serializeLString? _ _ _ hsb, i.property]
  | bnode b =>
      intro fuel bs rest hfuel h
      cases fuel with
      | zero => simp [tdepth] at hfuel
      | succ f =>
      rw [serializeInline?, Option.map_eq_some_iff] at h
      obtain ⟨sb, hsb, rfl⟩ := h
      rw [List.cons_append, parseInlineGo]
      simp [parseU8, tagIri, tagBnode,
        parseLString_serializeLString? _ _ _ hsb]
  | literal l =>
      intro fuel bs rest hfuel h
      cases fuel with
      | zero => simp [tdepth] at hfuel
      | succ f =>
      rw [serializeInline?] at h
      by_cases hfit : lexicalFitsInline l
      · simp only [hfit, Bool.not_true, Bool.false_eq_true, if_false] at h
        cases hlex : serializeLString? l.val.lexicalForm with
        | none => rw [hlex] at h; simp at h
        | some lexb =>
        cases hdt : serializeLString? l.val.datatype.val with
        | none => rw [hlex, hdt] at h; simp at h
        | some dtb =>
        cases hlang : serializeLangField? l.val.langTag l.val.direction with
        | none => rw [hlex, hdt, hlang] at h; simp at h
        | some langb =>
        rw [hlex, hdt, hlang] at h
        simp only [bind, Option.bind, Option.some.injEq] at h
        subst h
        have h1 := parseLString_serializeLString? l.val.lexicalForm lexb
          (dtb ++ (langb ++ rest)) hlex
        have h2 := parseLString_serializeLString? l.val.datatype.val dtb
          (langb ++ rest) hdt
        have h3 := parseLangField_serializeLangField? l.val.langTag
          l.val.direction langb rest hlang
        have happ : lexb ++ dtb ++ langb ++ rest
            = lexb ++ (dtb ++ (langb ++ rest)) := by simp [List.append_assoc]
        rw [List.cons_append, happ, parseInlineGo]
        simp only [bind, Option.bind, parseU8, h1, h2, h3, tagIri, tagBnode,
          tagLiteralInline]
        rw [if_neg (by decide), if_neg (by decide), if_pos (by decide)]
        have hnot : ¬ (maxInlineLexicalBytes < (bytesOfString l.val.lexicalForm).length) := by
          have := hfit
          rw [lexicalFitsInline, decide_eq_true_eq] at this
          omega
        simp only [hnot, if_false]
        have hmk := mkLiteralLocal_self l
        show Option.map (fun t => (t, rest))
          (mkLiteralLocal l.val.lexicalForm l.val.datatype.val l.val.langTag
            l.val.direction) = some (Term.literal l, rest)
        rw [hmk]
        rfl
      · simp only [hfit, Bool.not_false, if_true] at h
        exact absurd h (by simp)
  | tripleTerm s p o ih =>
      intro fuel bs rest hfuel h
      cases fuel with
      | zero => simp [tdepth] at hfuel
      | succ f =>
      rw [serializeInline?] at h
      cases hs : serializeSubject? s with
      | none => rw [hs] at h; simp at h
      | some sb =>
      cases hp : serializeLString? p.val with
      | none => rw [hs, hp] at h; simp at h
      | some pb =>
      cases ho : serializeInline? o with
      | none => rw [hs, hp, ho] at h; simp at h
      | some ob =>
      rw [hs, hp, ho] at h
      simp only [bind, Option.bind, Option.some.injEq] at h
      subst h
      have h1 := parseSubject_serializeSubject? s sb (pb ++ (ob ++ rest)) hs
      have h2 := parseLString_serializeLString? p.val pb (ob ++ rest) hp
      have hdo : tdepth o ≤ f := by
        simp only [tdepth] at hfuel
        omega
      have h3 := ih f ob rest hdo ho
      have happ : sb ++ pb ++ ob ++ rest = sb ++ (pb ++ (ob ++ rest)) := by
        simp [List.append_assoc]
      rw [List.cons_append, happ, parseInlineGo]
      simp only [bind, Option.bind, parseU8, h1, h2, h3, tagIri, tagBnode,
        tagLiteralInline, tagTripleTerm]
      rw [if_neg (by decide), if_neg (by decide), if_neg (by decide),
        if_pos (by decide), dif_pos p.property]

/-- The inline decoder inverts the inline encoder, with no fuel in the
statement. -/
theorem parseInline_serializeInline? (t : Term) (bs rest : List UInt8)
    (h : serializeInline? t = some bs) :
    parseInline (bs ++ rest) = some (t, rest) := by
  rw [parseInline]
  refine parseInlineGo_serializeInline? t _ bs rest ?_ h
  have := tdepth_le_length t bs h
  simp only [List.length_append]
  omega

/-! ## The blob round trip -/

private theorem drop8_writeU64LE (n : UInt64) (t : List UInt8) :
    (writeU64LE n ++ t).drop 8 = t := by
  simp [writeU64LE, writeU32LE]

theorem parseBlob_serializeBlob? (b : BlobLiteral) (bs rest : List UInt8)
    (h : serializeBlob? b = some bs) :
    parseBlob (bs ++ rest) = some (b, rest) := by
  rw [serializeBlob?] at h
  by_cases hsup : blobSupported b
  case neg => simp only [hsup, Bool.not_false, if_true] at h; exact absurd h (by simp)
  simp only [hsup, Bool.not_true, Bool.false_eq_true, if_false] at h
  cases hdt : serializeLString? b.datatype.val with
  | none => rw [hdt] at h; simp at h
  | some dtb =>
  cases hlang : serializeLangField? b.langTag b.direction with
  | none => rw [hdt, hlang] at h; simp at h
  | some langb =>
  rw [hdt, hlang] at h
  simp only [bind, Option.bind, Option.some.injEq] at h
  subst h
  -- the admission facts
  have hsupB : blobSupported b = true := hsup
  rw [blobSupported, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hsup
  obtain ⟨⟨⟨hlo, hhi⟩, hsize⟩, hwf⟩ := hsup
  have hlo' : maxInlineLexicalBytes < b.byteLength := by
    simpa using hlo
  have hhi' : b.byteLength ≤ maxBlobBytes := by simpa using hhi
  have hsize' : b.sha256.size = 32 := by simpa using hsize
  have hdigest : b.sha256.toList.length = 32 := by
    rw [byteArray_toList_eq, Array.length_toList]; exact hsize'
  have hlen : (UInt64.ofNat b.byteLength).toNat = b.byteLength := by
    have : b.byteLength < UInt64.size := by
      rw [maxBlobBytes] at hhi'
      have : (4294967296 : Nat) ≤ UInt64.size := by decide
      omega
    simp [UInt64.toNat_ofNat, Nat.mod_eq_of_lt this]
  have h1 := parseLString_serializeLString? b.datatype.val dtb
    (langb ++ (writeU64LE (UInt64.ofNat b.byteLength) ++ (b.sha256.toList ++ rest))) hdt
  have h2 := parseLangField_serializeLangField? b.langTag b.direction langb
    (writeU64LE (UInt64.ofNat b.byteLength) ++ (b.sha256.toList ++ rest)) hlang
  have happ : dtb ++ langb ++ writeU64LE (UInt64.ofNat b.byteLength) ++ b.sha256.toList ++ rest
      = dtb ++ (langb ++ (writeU64LE (UInt64.ofNat b.byteLength) ++
          (b.sha256.toList ++ rest))) := by simp [List.append_assoc]
  rw [List.cons_append, happ, parseBlob]
  simp only [bind, Option.bind, parseU8, h1, h2, tagLiteralBlob,
    bne_self_eq_false, Bool.false_eq_true, if_false]
  rw [readU64LE_writeU64LE_append, drop8_writeU64LE]
  simp only [bind, Option.bind]
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
    List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega),
    List.nil_append]
  simp only [hdigest, bne_self_eq_false, Bool.false_eq_true, if_false]
  rw [dif_pos b.datatype.property]
  have hba : ByteArray.mk b.sha256.toList.toArray = b.sha256 := by
    rw [byteArray_toList_eq, Array.toArray_toList]
  have hrebuilt :
      ({ datatype := ⟨b.datatype.val, b.datatype.property⟩,
         langTag := b.langTag, direction := b.direction,
         byteLength := (UInt64.ofNat b.byteLength).toNat,
         sha256 := ByteArray.mk b.sha256.toList.toArray } : BlobLiteral) = b := by
    rw [hlen, hba]
  rw [hrebuilt, if_pos hsupB]

/-! ## The term round trip -/

/-- The v2 decoder inverts the v2 encoder, with arbitrary trailing bytes
present. There is no admission hypothesis: `serializeTerm?` is its own
admission test and `parseTerm` tests the same conditions. -/
theorem parseTerm_serializeTerm? (w : WireTerm) (bs rest : List UInt8)
    (h : serializeTerm? w = some bs) :
    parseTerm (bs ++ rest) = some (w, rest) := by
  cases w with
  | inline t =>
      rw [serializeTerm?] at h
      have hpar := parseInline_serializeInline? t bs rest h
      -- the first byte of an inline encoding is never the blob tag
      have hhead : ∃ tag tail, bs = tag :: tail ∧ tag ≠ tagLiteralBlob := by
        cases t with
        | iri i =>
            rw [serializeInline?, Option.map_eq_some_iff] at h
            obtain ⟨sb, _, rfl⟩ := h
            exact ⟨tagIri, sb, rfl, by decide⟩
        | bnode b =>
            rw [serializeInline?, Option.map_eq_some_iff] at h
            obtain ⟨sb, _, rfl⟩ := h
            exact ⟨tagBnode, sb, rfl, by decide⟩
        | literal l =>
            rw [serializeInline?] at h
            by_cases hfit : lexicalFitsInline l
            · simp only [hfit, Bool.not_true, Bool.false_eq_true, if_false] at h
              cases hlex : serializeLString? l.val.lexicalForm with
              | none => rw [hlex] at h; simp at h
              | some lexb =>
              cases hdt : serializeLString? l.val.datatype.val with
              | none => rw [hlex, hdt] at h; simp at h
              | some dtb =>
              cases hlang : serializeLangField? l.val.langTag l.val.direction with
              | none => rw [hlex, hdt, hlang] at h; simp at h
              | some langb =>
              rw [hlex, hdt, hlang] at h
              simp only [bind, Option.bind, Option.some.injEq] at h
              exact ⟨tagLiteralInline, lexb ++ dtb ++ langb, h.symm, by decide⟩
            · simp only [hfit, Bool.not_false, if_true] at h
              exact absurd h (by simp)
        | tripleTerm s p o =>
            rw [serializeInline?] at h
            cases hs : serializeSubject? s with
            | none => rw [hs] at h; simp at h
            | some sb =>
            cases hp : serializeLString? p.val with
            | none => rw [hs, hp] at h; simp at h
            | some pb =>
            cases ho : serializeInline? o with
            | none => rw [hs, hp, ho] at h; simp at h
            | some ob =>
            rw [hs, hp, ho] at h
            simp only [bind, Option.bind, Option.some.injEq] at h
            exact ⟨tagTripleTerm, sb ++ pb ++ ob, h.symm, by decide⟩
      obtain ⟨tag, tail, hbs, htag⟩ := hhead
      rw [hbs, List.cons_append, parseTerm]
      rw [if_neg (by simpa using htag)]
      rw [← List.cons_append, ← hbs, hpar]
      rfl
  | blob b =>
      rw [serializeTerm?] at h
      have hpar := parseBlob_serializeBlob? b bs rest h
      have hbs : ∃ tail, bs = tagLiteralBlob :: tail := by
        rw [serializeBlob?] at h
        by_cases hsup : blobSupported b
        · simp only [hsup, Bool.not_true, Bool.false_eq_true, if_false] at h
          cases hdt : serializeLString? b.datatype.val with
          | none => rw [hdt] at h; simp at h
          | some dtb =>
          cases hlang : serializeLangField? b.langTag b.direction with
          | none => rw [hdt, hlang] at h; simp at h
          | some langb =>
          rw [hdt, hlang] at h
          simp only [bind, Option.bind, Option.some.injEq] at h
          exact ⟨dtb ++ langb ++ writeU64LE (UInt64.ofNat b.byteLength) ++
            b.sha256.toList, h.symm⟩
        · simp only [hsup, Bool.not_false, if_true] at h
          exact absurd h (by simp)
      obtain ⟨tail, hbs⟩ := hbs
      rw [hbs, List.cons_append, parseTerm]
      rw [if_pos (by simp)]
      rw [← List.cons_append, ← hbs, hpar]
      rfl

/-- Every v2 encoding starts with a tag byte, so it is never empty. The
paged dictionary's page framing needs this. -/
theorem serializeTerm?_ne_nil (w : WireTerm) (bs : List UInt8)
    (h : serializeTerm? w = some bs) : bs ≠ [] := by
  intro hnil
  have hpar := parseTerm_serializeTerm? w bs [] h
  rw [hnil] at hpar
  simp [parseTerm] at hpar

/-! ## The canonical tag choice -/

/-- Section 4.1, one direction: a literal at or below the inline ceiling
is written inline. -/
theorem toWire_inline_iff (h : ByteArray → ByteArray) (l : WfLiteral) :
    toWire h (.literal l) = .inline (.literal l) ↔
      (bytesOfString l.val.lexicalForm).length ≤ maxInlineLexicalBytes := by
  rw [toWire]
  by_cases hfit : lexicalFitsInline l
  · rw [if_pos hfit]
    have : (bytesOfString l.val.lexicalForm).length ≤ maxInlineLexicalBytes := by
      rw [lexicalFitsInline, decide_eq_true_eq] at hfit; exact hfit
    simp [this]
  · rw [if_neg hfit]
    have : ¬ ((bytesOfString l.val.lexicalForm).length ≤ maxInlineLexicalBytes) := by
      rw [lexicalFitsInline] at hfit; simpa using hfit
    simp [this]

/-- Section 4.1, the other direction: a literal above the inline ceiling
is written out-of-line. -/
theorem toWire_blob_iff (h : ByteArray → ByteArray) (l : WfLiteral) :
    (∃ b, toWire h (.literal l) = .blob b) ↔
      maxInlineLexicalBytes < (bytesOfString l.val.lexicalForm).length := by
  rw [toWire]
  by_cases hfit : lexicalFitsInline l
  · rw [if_pos hfit]
    have : (bytesOfString l.val.lexicalForm).length ≤ maxInlineLexicalBytes := by
      rw [lexicalFitsInline, decide_eq_true_eq] at hfit; exact hfit
    constructor
    · rintro ⟨b, hb⟩; exact absurd hb (by simp)
    · intro hlt; omega
  · rw [if_neg hfit]
    have : ¬ ((bytesOfString l.val.lexicalForm).length ≤ maxInlineLexicalBytes) := by
      rw [lexicalFitsInline] at hfit; simpa using hfit
    constructor
    · intro _; omega
    · intro _; exact ⟨_, rfl⟩

/-- A non-literal term is always inline. -/
theorem toWire_iri (h : ByteArray → ByteArray) (i : WfIri) :
    toWire h (.iri i) = .inline (.iri i) := rfl

theorem toWire_bnode (h : ByteArray → ByteArray) (b : BNodeId) :
    toWire h (.bnode b) = .inline (.bnode b) := rfl

theorem toWire_tripleTerm (h : ByteArray → ByteArray) (s : Subject) (p : WfIri)
    (o : Term) : toWire h (.tripleTerm s p o) = .inline (.tripleTerm s p o) := rfl

/-! ## Resolution -/

private theorem size_toUTF8 (s : String) : s.toUTF8.size = (bytesOfString s).length := by
  rw [bytesOfString, byteArray_toList_eq, Array.length_toList]
  rfl

/-- The packer's obligation: a term written by `toWire` and resolved
through its own lexical bytes is that term again, for any hash
function. -/
theorem resolve_toWire (h : ByteArray → ByteArray) (t : Term) :
    resolve h (lookupOf h t) (toWire h t) = some t := by
  cases t with
  | iri i => rfl
  | bnode b => rfl
  | tripleTerm s p o => rfl
  | literal l =>
      rw [toWire]
      by_cases hfit : lexicalFitsInline l
      · rw [if_pos hfit]; rfl
      · rw [if_neg hfit]
        have hlk : lookupOf h (Term.literal l) (h l.val.lexicalForm.toUTF8)
            = some l.val.lexicalForm.toUTF8 := by simp [lookupOf]
        have hutf : String.fromUTF8? l.val.lexicalForm.toUTF8
            = some l.val.lexicalForm := by
          have hb := stringOfBytes?_bytesOfString l.val.lexicalForm
          rw [stringOfBytes?, bytesOfString, byteArray_toList_eq,
            Array.toArray_toList] at hb
          exact hb
        have hrec :
            ({ lexicalForm := l.val.lexicalForm,
               datatype := l.val.datatype, langTag := l.val.langTag,
               direction := l.val.direction } : Literal) = l.val := rfl
        rw [resolve]
        simp only [hlk, bind, Option.bind, size_toUTF8, bne_self_eq_false,
          Bool.false_eq_true, if_false, ne_eq, not_true_eq_false, hutf, hrec]
        rw [dif_pos l.property]

#print axioms parseLangField_serializeLangField?
#print axioms tdepth_le_length
#print axioms parseInline_serializeInline?
#print axioms parseBlob_serializeBlob?
#print axioms parseTerm_serializeTerm?
#print axioms serializeTerm?_ne_nil
#print axioms toWire_inline_iff
#print axioms toWire_blob_iff
#print axioms resolve_toWire

end L4Factoidal.Storage.TermWireV2
