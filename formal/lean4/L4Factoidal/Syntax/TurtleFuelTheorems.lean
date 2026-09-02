/-
L4Factoidal.Syntax.TurtleFuelTheorems — the literal-body loops of the Turtle
parser do not depend on their fuel above the remaining length.

`readShortStringBody`, `readLongStringBody` and `collectNum` are bounded
loops in the F* style: a fuel argument guards termination, and every step
consumes at least one character. This module proves that any two fuels
above the remaining length give the same result, and draws the corollary
that the parser's constant `literalFuel` (`Syntax.Turtle`) computes exactly
the specification forms `readTurtleStringSpec` and `readNumericLiteralSpec`,
which take their fuel from the remaining length as the F* source does.

Why the constant: computing `cs.length + 1` once per literal traversed the
rest of the document at every token and made `parseTurtle` quadratic
(2026-09-02). The specification forms are kept as the meaning; the constant
is the implementation, and this file is the bridge.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Syntax.Turtle

namespace L4Factoidal.Syntax

/-- An assembled numeric escape returns the tail it was given. -/
theorem escapeResult_ok {cp pos k pos' : Nat} {r0 r : List Char} {c : Char}
    (h : escapeResult cp pos k r0 = .ok (c, pos', r)) : r = r0 := by
  unfold escapeResult at h
  split at h
  · simp at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2.2.symm

/-- An accepted escape consumes at least its escape letter, so the
remainder is shorter than the list after the backslash. -/
theorem decodeEscape_length {pos : Nat} {rest : List Char} {c : Char} {pos' : Nat}
    {r : List Char} (h : decodeEscape pos rest = .ok (c, pos', r)) :
    r.length < rest.length := by
  unfold decodeEscape at h
  split at h
  case h_9 =>
    rename_i h0 h1 h2 h3 r0
    generalize hexVal h0 = v0 at h
    generalize hexVal h1 = v1 at h
    generalize hexVal h2 = v2 at h
    generalize hexVal h3 = v3 at h
    cases v0 with
    | none => simp at h
    | some d0 =>
    cases v1 with
    | none => simp at h
    | some d1 =>
    cases v2 with
    | none => simp at h
    | some d2 =>
    cases v3 with
    | none => simp at h
    | some d3 =>
    dsimp only at h
    rw [escapeResult_ok h]
    simp only [List.length_cons]
    omega
  case h_11 =>
    rename_i h0 h1 h2 h3 h4 h5 h6 h7 r0
    generalize hexVal h0 = v0 at h
    generalize hexVal h1 = v1 at h
    generalize hexVal h2 = v2 at h
    generalize hexVal h3 = v3 at h
    generalize hexVal h4 = v4 at h
    generalize hexVal h5 = v5 at h
    generalize hexVal h6 = v6 at h
    generalize hexVal h7 = v7 at h
    cases v0 with
    | none => simp at h
    | some d0 =>
    cases v1 with
    | none => simp at h
    | some d1 =>
    cases v2 with
    | none => simp at h
    | some d2 =>
    cases v3 with
    | none => simp at h
    | some d3 =>
    cases v4 with
    | none => simp at h
    | some d4 =>
    cases v5 with
    | none => simp at h
    | some d5 =>
    cases v6 with
    | none => simp at h
    | some d6 =>
    cases v7 with
    | none => simp at h
    | some d7 =>
    dsimp only at h
    rw [escapeResult_ok h]
    simp only [List.length_cons]
    omega
  all_goals first
    | (simp only [Except.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨-, -, rfl⟩ := h
       simp)
    | simp at h

/-- The short-form string loop is the same function for every fuel above
the remaining length. -/
theorem readShortStringBody_fuel_indep (q : Char) :
    ∀ (n : Nat) (cs : List Char), cs.length ≤ n →
      ∀ (f1 f2 pos : Nat) (acc : List Char), cs.length < f1 → cs.length < f2 →
        readShortStringBody q f1 pos cs acc = readShortStringBody q f2 pos cs acc := by
  intro n
  induction n with
  | zero =>
      intro cs hcs f1 f2 pos acc h1 h2
      have : cs = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hcs)
      subst this
      cases f1 with
      | zero => omega
      | succ f1 =>
        cases f2 with
        | zero => omega
        | succ f2 => rfl
  | succ n ih =>
      intro cs hcs f1 f2 pos acc h1 h2
      cases f1 with
      | zero => omega
      | succ f1 =>
      cases f2 with
      | zero => omega
      | succ f2 =>
      cases cs with
      | nil => rfl
      | cons c rest =>
        simp only [List.length_cons] at h1 h2 hcs
        simp only [readShortStringBody]
        split
        · rfl
        · rfl
        · rfl
        · rename_i cs' rest' heq
          obtain ⟨rfl, rfl⟩ := List.cons.inj heq
          cases hd : decodeEscape pos rest with
          | error e => rfl
          | ok v =>
            obtain ⟨c', pos', r⟩ := v
            have hr := decodeEscape_length hd
            dsimp only
            exact ih r (by omega) f1 f2 pos' (c' :: acc) (by omega) (by omega)
        · rename_i cs' c' rest' hx1 hx2 hx3 heq
          obtain ⟨rfl, rfl⟩ := List.cons.inj heq
          split
          · rfl
          · exact ih _ (by omega) f1 f2 (pos + 1) _ (by omega) (by omega)

/-- The long-form string loop is the same function for every fuel above
the remaining length. -/
theorem readLongStringBody_fuel_indep (q : Char) :
    ∀ (n : Nat) (cs : List Char), cs.length ≤ n →
      ∀ (f1 f2 pos : Nat) (acc : List Char), cs.length < f1 → cs.length < f2 →
        readLongStringBody q f1 pos cs acc = readLongStringBody q f2 pos cs acc := by
  intro n
  induction n with
  | zero =>
      intro cs hcs f1 f2 pos acc h1 h2
      have : cs = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hcs)
      subst this
      cases f1 with
      | zero => omega
      | succ f1 =>
        cases f2 with
        | zero => omega
        | succ f2 => rfl
  | succ n ih =>
      intro cs hcs f1 f2 pos acc h1 h2
      cases f1 with
      | zero => omega
      | succ f1 =>
      cases f2 with
      | zero => omega
      | succ f2 =>
      cases cs with
      | nil => rfl
      | cons c rest =>
        simp only [List.length_cons] at h1 h2 hcs
        simp only [readLongStringBody]
        split
        · rfl
        · rename_i cs' rest' heq
          obtain ⟨rfl, rfl⟩ := List.cons.inj heq
          cases hd : decodeEscape pos rest with
          | error e => rfl
          | ok v =>
            obtain ⟨c', pos', r⟩ := v
            have hr := decodeEscape_length hd
            dsimp only
            exact ih r (by omega) f1 f2 pos' (c' :: acc) (by omega) (by omega)
        · rename_i cs' c' rest' hx heq
          obtain ⟨rfl, rfl⟩ := List.cons.inj heq
          split
          · split
            · split
              · rfl
              · exact ih _ (by omega) f1 f2 (pos + 1) _ (by omega) (by omega)
            · exact ih _ (by omega) f1 f2 (pos + 1) _ (by omega) (by omega)
          · exact ih _ (by omega) f1 f2 (pos + 1) _ (by omega) (by omega)

/-- [17] String is the same function for every fuel above the remaining
length. -/
theorem readTurtleStringWith_fuel_indep (f1 f2 pos : Nat) (cs : List Char)
    (h1 : cs.length < f1) (h2 : cs.length < f2) :
    readTurtleStringWith f1 pos cs = readTurtleStringWith f2 pos cs := by
  unfold readTurtleStringWith
  split
  · exact readLongStringBody_fuel_indep _ _ _ (Nat.le_refl _) f1 f2 _ _
      (by simp only [List.length_cons] at h1; omega) (by simp only [List.length_cons] at h2; omega)
  · exact readLongStringBody_fuel_indep _ _ _ (Nat.le_refl _) f1 f2 _ _
      (by simp only [List.length_cons] at h1; omega) (by simp only [List.length_cons] at h2; omega)
  · exact readShortStringBody_fuel_indep _ _ _ (Nat.le_refl _) f1 f2 _ _
      (by simp only [List.length_cons] at h1; omega) (by simp only [List.length_cons] at h2; omega)
  · exact readShortStringBody_fuel_indep _ _ _ (Nat.le_refl _) f1 f2 _ _
      (by simp only [List.length_cons] at h1; omega) (by simp only [List.length_cons] at h2; omega)
  · rfl

/-- The parser's constant-fuel string reader computes the specification
form for every input shorter than `literalFuel`. -/
theorem readTurtleString_eq_spec (pos : Nat) (cs : List Char) (h : cs.length < literalFuel) :
    readTurtleString pos cs = readTurtleStringSpec pos cs :=
  readTurtleStringWith_fuel_indep _ _ pos cs h (Nat.lt_succ_self _)


/-- The numeric collector is the same function for every fuel above the
remaining length. -/
theorem collectNum_fuel_indep :
    ∀ (n : Nat) (cs : List Char), cs.length ≤ n →
      ∀ (f1 f2 pos : Nat) (acc : List Char) (hasDot hasE : Bool),
        cs.length < f1 → cs.length < f2 →
        collectNum f1 pos cs acc hasDot hasE = collectNum f2 pos cs acc hasDot hasE := by
  intro n
  induction n with
  | zero =>
      intro cs hcs f1 f2 pos acc hasDot hasE h1 h2
      have : cs = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hcs)
      subst this
      cases f1 with
      | zero => omega
      | succ f1 =>
        cases f2 with
        | zero => omega
        | succ f2 => rfl
  | succ n ih =>
      intro cs hcs f1 f2 pos acc hasDot hasE h1 h2
      cases f1 with
      | zero => omega
      | succ f1 =>
      cases f2 with
      | zero => omega
      | succ f2 =>
      cases cs with
      | nil => rfl
      | cons c rest =>
        simp only [List.length_cons] at h1 h2 hcs
        simp only [collectNum]
        split
        · exact ih _ (by omega) f1 f2 _ _ _ _ (by omega) (by omega)
        · split
          · split
            · rfl
            · split
              · exact ih _ (by (try simp only [List.length_cons] at *); omega) f1 f2 _ _ _ _
                  (by (try simp only [List.length_cons] at *); omega)
                  (by (try simp only [List.length_cons] at *); omega)
              · split
                · exact ih _ (by (try simp only [List.length_cons] at *); omega) f1 f2 _ _ _ _
                    (by (try simp only [List.length_cons] at *); omega)
                    (by (try simp only [List.length_cons] at *); omega)
                · rfl
          · split
            · split
              · rfl
              · split
                · exact ih _ (by (try simp only [List.length_cons] at *); omega) f1 f2 _ _ _ _
                    (by (try simp only [List.length_cons] at *); omega)
                    (by (try simp only [List.length_cons] at *); omega)
                · split
                  · exact ih _ (by (try simp only [List.length_cons] at *); omega) f1 f2 _ _ _ _
                      (by (try simp only [List.length_cons] at *); omega)
                      (by (try simp only [List.length_cons] at *); omega)
                  · rfl
            · rfl

/-- Stripping the optional sign does not lengthen the input. -/
theorem numericSign_tail_length (pos : Nat) (cs : List Char) :
    (numericSign pos cs).2.2.length ≤ cs.length := by
  unfold numericSign
  split <;> simp

/-- [16] NumericLiteral is the same function for every fuel above the
length of the input after the optional sign. -/
theorem readNumericLiteralWith_fuel_indep (f1 f2 pos : Nat) (cs : List Char)
    (h1 : (numericSign pos cs).2.2.length < f1) (h2 : (numericSign pos cs).2.2.length < f2) :
    readNumericLiteralWith f1 pos cs = readNumericLiteralWith f2 pos cs := by
  unfold readNumericLiteralWith
  generalize hs : numericSign pos cs = t at h1 h2 ⊢
  obtain ⟨signStr, pos0, cs0⟩ := t
  dsimp only at h1 h2 ⊢
  split
  · split
    · split
      · rfl
      · rename_i _ d rest _
        rw [collectNum_fuel_indep _ (d :: rest) (Nat.le_refl _) f1 f2 (pos0 + 1) ['.'] true false
          (by simp only [List.length_cons] at h1 ⊢; omega)
          (by simp only [List.length_cons] at h2 ⊢; omega)]
    · rfl
  · rw [collectNum_fuel_indep cs0.length cs0 (Nat.le_refl _) f1 f2 pos0 [] false false h1 h2]

/-- The parser's constant-fuel numeric reader computes the specification
form for every input shorter than `literalFuel`. -/
theorem readNumericLiteral_eq_spec (pos : Nat) (cs : List Char) (h : cs.length < literalFuel) :
    readNumericLiteral pos cs = readNumericLiteralSpec pos cs :=
  readNumericLiteralWith_fuel_indep _ _ pos cs
    (Nat.lt_of_le_of_lt (numericSign_tail_length pos cs) h) (Nat.lt_succ_self _)

#print axioms decodeEscape_length
#print axioms readShortStringBody_fuel_indep
#print axioms readLongStringBody_fuel_indep
#print axioms collectNum_fuel_indep
#print axioms readTurtleString_eq_spec
#print axioms readNumericLiteral_eq_spec

end L4Factoidal.Syntax
