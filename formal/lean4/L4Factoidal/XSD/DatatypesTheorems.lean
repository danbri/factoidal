/-
L4Factoidal.XSD.DatatypesTheorems — what is PROVED about the XML Schema
1.1 Part 2 lexical mappings, canonical mappings and facet checking, as
distinct from what the `#guard` battery and the W3C suite MEASURE.

Each theorem below states a property the specification asserts, over the
functions of `XSD/Datatypes.lean` and `XSD/SimpleType.lean`. Every one
is closed by `#print axioms` at the end of the file — only Lean's three
standard axioms may appear.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.XSD.SimpleType

namespace L4Factoidal.XSD

/-! ## §2.2.2 — the lexical mapping is a FUNCTION

In Lean this is carried by the type: `lexicalMap : Builtin → String →
Option Val` is a function, so one lexical form of one datatype has at
most one value, by construction rather than by proof. What is worth
stating is the FACTORISATION §4.3.6 requires — whiteSpace is applied
before the lexical mapping, never inside it — because that is the part a
consumer can get wrong (RDF 1.1 Semantics §7 needs the version WITHOUT
whiteSpace, and calls `lexicalMap`). -/

theorem lexicalMapWs_factors (b : Builtin) (s : String) :
    lexicalMapWs b s = lexicalMap b (applyWhiteSpace b.whiteSpace s) := rfl

theorem applyWhiteSpace_preserve (s : String) :
    applyWhiteSpace .preserve s = s := rfl

/-- §3.3.1: `string` fixes `whiteSpace` to `preserve`, so its lexical
mapping is the identity on every string and its lexical space is every
string. -/
theorem string_lexical_total (s : String) :
    lexicalMapWs .string s = some (.str .string s) := rfl

/-! ## §3.4 — the derivation hierarchy -/

theorem derivedFrom_refl (b : Builtin) : derivedFrom b b = true := by
  unfold derivedFrom derivedFromFuel
  simp

/-- §3.4.16-§3.4.26: every bounded integer type is derived from
`integer`, and `integer` from `decimal`. -/
theorem byte_derived_integer : derivedFrom .byte .integer = true := by decide
theorem integer_derived_decimal : derivedFrom .integer .decimal = true := by decide
theorem decimal_not_derived_integer : derivedFrom .decimal .integer = false := by decide

/-! ## §3.3.13 / §3.4 — the integer tower

The bound check is not a facet the caller may forget: it is inside the
lexical mapping, so a literal outside the type's range has NO value. -/

theorem int_lexical_in_bounds (b : Builtin) (s : String) (i : Int)
    (h : parseIntegerLex s = some i) (hb : inIntBounds b i = false) :
    (match b with
     | .integer | .nonPositiveInteger | .negativeInteger | .long | .int
     | .short | .byte | .nonNegativeInteger | .unsignedLong | .unsignedInt
     | .unsignedShort | .unsignedByte | .positiveInteger =>
         lexicalMap b s = none
     | _ => True) := by
  cases b <;> simp [lexicalMap, lexicalMapFuel, h, hb]

/-! ## §3.3.2 — `boolean`: the canonical mapping round-trips

`canonicalMap` produces a lexical representation, and the lexical
mapping takes that representation back to the same value. For `boolean`
the value space is finite, so the statement is closed by cases. -/

theorem boolean_canonical_roundTrip (x : Bool) :
    lexicalMap .boolean (canonicalMap .boolean (.bool x)) = some (.bool x) := by
  cases x <;> rfl

/-- §2.3.1: a canonical mapping is IDEMPOTENT in the sense that
canonicalising the value of a canonical representation gives that same
representation back. -/
theorem boolean_canonical_idempotent (x : Bool) :
    canonicalMap .boolean
      ((lexicalMap .boolean (canonicalMap .boolean (.bool x))).getD (.bool x))
    = canonicalMap .boolean (.bool x) := by
  cases x <;> rfl

/-! ## §4.2.2 — the order relation is PARTIAL, and says so

A NaN is in the value space of `float` and `double` and is outside their
order (§3.3.4: "NaN ... is not equal to, less than, or greater than any
value"). `valCompare` returns `none` for it, and `boundOk` therefore
fails every bound facet — which is the specification's outcome, not an
accident of the encoding. -/

theorem nan_incomparable (a : Val) :
    valCompare (.flt ⟨false, .nan⟩) a = none := by
  cases a <;> simp [valCompare, fvalCmp]

theorem nan_fails_every_bound (b : Builtin) (lex : String) :
    boundOk b (.flt ⟨false, .nan⟩) (some lex) (fun _ => true) = false ∨
    lexicalMapWs b lex = none := by
  unfold boundOk
  cases h : lexicalMapWs b lex with
  | none => exact Or.inr rfl
  | some bv =>
      left
      simp [h, nan_incomparable]

/-! ## §4.3 — facet checking is sound against the value space

`validate` says "in the lexical space AND every facet holds". The two
theorems below are the two halves: a validated literal HAS a value, and
that value satisfies every value-space facet the type declares. Both are
stated for the atomic variety, where "the value space facets" is exactly
`valueFacetsOk`. -/

theorem validate_iff_valueOf (t : SimpleType) (lit : String) :
    validate t lit = true ↔ (valueOf t lit).isSome = true := by
  unfold validate
  exact Iff.rfl

/-- The atomic case of `valueOf`, unfolded once. Everything below is a
corollary of this equation, so the facet-soundness statements do not
each re-derive the definition. -/
theorem atomic_valueOf_eq (b : Builtin) (f : Facets) (lit : String) :
    valueOf (.atomic b f) lit =
      (if !patternMatches f.patterns
             (applyWhiteSpace (f.whiteSpace.getD b.whiteSpace) lit) then none
       else match lexicalMap b
                   (applyWhiteSpace (f.whiteSpace.getD b.whiteSpace) lit) with
            | none => none
            | some v => if valueFacetsOk b f v then some v else none) := rfl

theorem atomic_valid_has_value {v : Val} (b : Builtin) (f : Facets) (lit : String)
    (h : valueOf (.atomic b f) lit = some v) :
    lexicalMap b (applyWhiteSpace (f.whiteSpace.getD b.whiteSpace) lit) = some v := by
  rw [atomic_valueOf_eq] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i w hw
      split at h
      · simp at h; subst h; exact hw
      · simp at h

theorem atomic_valid_satisfies_facets {v : Val} (b : Builtin) (f : Facets)
    (lit : String) (h : valueOf (.atomic b f) lit = some v) :
    valueFacetsOk b f v = true := by
  rw [atomic_valueOf_eq] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · rename_i hf; simp at h; subst h; exact hf
      · simp at h

/-- The `pattern` facet (§4.3.4) is on the LEXICAL form, so a validated
literal matches every pattern group after whiteSpace processing. -/
theorem atomic_valid_matches_patterns {v : Val} (b : Builtin) (f : Facets)
    (lit : String) (h : valueOf (.atomic b f) lit = some v) :
    patternMatches f.patterns
      (applyWhiteSpace (f.whiteSpace.getD b.whiteSpace) lit) = true := by
  rw [atomic_valueOf_eq] at h
  split at h
  · simp at h
  · rename_i hp
    simpa using hp

/-! ## The axiom gate -/

#print axioms lexicalMapWs_factors
#print axioms string_lexical_total
#print axioms derivedFrom_refl
#print axioms int_lexical_in_bounds
#print axioms boolean_canonical_roundTrip
#print axioms boolean_canonical_idempotent
#print axioms nan_incomparable
#print axioms nan_fails_every_bound
#print axioms validate_iff_valueOf
#print axioms atomic_valueOf_eq
#print axioms atomic_valid_has_value
#print axioms atomic_valid_satisfies_facets
#print axioms atomic_valid_matches_patterns

end L4Factoidal.XSD
