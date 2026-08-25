/-
L4Factoidal.Syntax.LocalityLiteral — locality for the string-literal,
language-tag and datatype readers.

A reader is LOCAL when a run that stopped inside its input answers the
same on longer input, with the remainder grown by exactly what was
appended. That is the property the streaming N-Quads fold needs: a chunk
boundary must not change how the text before it parses.

The string-literal reader used to be blocked here. `readStringLiteralBody`
was one nineteen-arm recursion, so Lean could not generate its equation
lemmas and nothing downstream could rewrite with it —
<https://github.com/danbri/factoidal/issues/574>, the same wall as
<https://github.com/danbri/factoidal/issues/565> one reader over. Two
refactors cleared it, both behaviour-preserving and both gated by the
`#guard` table against `readStringLiteralBodyLegacy` in `Syntax.Lexing`:

* the step/recursion split (`strLitNextStep` + a three-arm
  `readStringLiteralBody`), which gave the recursion usable equations;
* `hex4` / `hex8`, which collapse the `\u` and `\U` arms from four and
  eight `Option Nat` scrutinees to one each. Before that, a proof about
  those arms split into 16 and 256 cases; a `simp_all` over them reached
  10.5-12 GB and took SIGKILL, measured three ways.

What the split still does not give is the guards. Lean's equation
compiler turns overlapping patterns into a case tree, so an arm reached
only because the earlier arms failed does not carry "the character was
not a quote" as a hypothesis. `strLitNextStep_plain` and
`strLitNextStep_badEscape` state those guards explicitly and are proved
by splitting the definition once.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.Syntax.Locality

namespace L4Factoidal.Syntax

/-! ## Shape lemmas the equation compiler does not hand back -/

theorem strLitNextStep_plain (pos : Nat) (c : Char) (rest : List Char)
    (h1 : c ≠ '"') (h2 : c ≠ '\\') (h3 : c ≠ '\n') (h4 : c ≠ '\r') :
    strLitNextStep pos (c :: rest) = .emit c 1 rest := by
  unfold strLitNextStep
  split <;> simp_all

theorem strLitNextStep_badEscape (pos : Nat) (e : Char) (t : List Char)
    (h1 : e ≠ 't') (h2 : e ≠ 'b') (h3 : e ≠ 'n') (h4 : e ≠ 'r') (h5 : e ≠ 'f')
    (h6 : e ≠ '"') (h7 : e ≠ '\'') (h8 : e ≠ '\\') (h9 : e ≠ 'u') (h10 : e ≠ 'U') :
    strLitNextStep pos ('\\' :: e :: t) = .fail ⟨s!"invalid escape: \\{e}", pos⟩ := by
  unfold strLitNextStep
  split <;> grind

/-! ## Discharging the arms that cannot emit -/

private theorem failNotEmit {pos : Nat} {cs : List Char} {c : Char} {w : Nat}
    {rest : List Char} (hf : ∃ e, strLitNextStep pos cs = .fail e)
    (h : strLitNextStep pos cs = .emit c w rest) : False := by
  obtain ⟨e, he⟩ := hf; rw [he] at h; simp at h

private theorem closeNotEmit {pos : Nat} {cs : List Char} {c : Char} {w : Nat}
    {rest : List Char} (hc : ∃ r, strLitNextStep pos cs = .close r)
    (h : strLitNextStep pos cs = .emit c w rest) : False := by
  obtain ⟨r, hr⟩ := hc; rw [hr] at h; simp at h

/-- An arm whose emitted character, width and remainder are all fixed by
the matched prefix: read the arm off both inputs, then transport `h`. -/
private theorem emitArm {pos : Nat} {cs extra rest r : List Char} {c c' : Char}
    {w w' : Nat}
    (hL : strLitNextStep pos cs = .emit c' w' r)
    (hR : strLitNextStep pos (cs ++ extra) = .emit c' w' (r ++ extra))
    (h : strLitNextStep pos cs = .emit c w rest) :
    strLitNextStep pos (cs ++ extra) = .emit c w (rest ++ extra) := by
  rw [hL] at h
  injection h with e1 e2 e3
  subst e1; subst e2; subst e3
  exact hR

theorem strLitEmitAt_local (cp pos width : Nat) (rest extra : List Char)
    (c : Char) (w : Nat) (r : List Char)
    (h : strLitEmitAt cp pos width rest = .emit c w r) :
    strLitEmitAt cp pos width (rest ++ extra) = .emit c w (r ++ extra) := by
  unfold strLitEmitAt at h ⊢
  split at h
  · simp at h
  · simp_all

/-! ## Emit locality

Every arm that emits consumes a prefix of FIXED length, and every arm it
had to get past to be reached is decided by that same prefix. Appending
to the input therefore cannot change which arm fires, and the remainder
grows by exactly what was appended. -/

theorem strLitNextStep_emit_local (pos : Nat) (cs extra rest : List Char)
    (c : Char) (w : Nat) (h : strLitNextStep pos cs = .emit c w rest) :
    strLitNextStep pos (cs ++ extra) = .emit c w (rest ++ extra) := by
  match cs with
  | [] => exact (failNotEmit ⟨_, rfl⟩ h).elim
  | c0 :: t =>
    by_cases hq : c0 = '"'
    · subst hq; exact (closeNotEmit ⟨_, rfl⟩ h).elim
    by_cases hnl : c0 = '\n'
    · subst hnl; exact (failNotEmit ⟨_, rfl⟩ h).elim
    by_cases hcr : c0 = '\r'
    · subst hcr; exact (failNotEmit ⟨_, rfl⟩ h).elim
    by_cases hbs : c0 = '\\'
    · subst hbs
      match t with
      | [] => exact (failNotEmit ⟨_, rfl⟩ h).elim
      | e :: t2 =>
        by_cases het : e = 't'
        · subst het; exact emitArm rfl rfl h
        by_cases heb : e = 'b'
        · subst heb; exact emitArm rfl rfl h
        by_cases hen : e = 'n'
        · subst hen; exact emitArm rfl rfl h
        by_cases her : e = 'r'
        · subst her; exact emitArm rfl rfl h
        by_cases hef : e = 'f'
        · subst hef; exact emitArm rfl rfl h
        by_cases hedq : e = '"'
        · subst hedq; exact emitArm rfl rfl h
        by_cases hesq : e = '\''
        · subst hesq; exact emitArm rfl rfl h
        by_cases hebs : e = '\\'
        · subst hebs; exact emitArm rfl rfl h
        by_cases heu : e = 'u'
        · subst heu
          match t2 with
          | [] => exact (failNotEmit ⟨_, rfl⟩ h).elim
          | [_] => exact (failNotEmit ⟨_, rfl⟩ h).elim
          | [_, _] => exact (failNotEmit ⟨_, rfl⟩ h).elim
          | [_, _, _] => exact (failNotEmit ⟨_, rfl⟩ h).elim
          | a :: b :: c2 :: d :: t3 =>
              have hL : strLitNextStep pos ('\\' :: 'u' :: a :: b :: c2 :: d :: t3)
                  = (match hex4 a b c2 d with
                     | some cp => strLitEmitAt cp pos 6 t3
                     | none => .fail ⟨"invalid hex digit in \\u escape", pos⟩) := rfl
              have hR : strLitNextStep pos (('\\' :: 'u' :: a :: b :: c2 :: d :: t3) ++ extra)
                  = (match hex4 a b c2 d with
                     | some cp => strLitEmitAt cp pos 6 (t3 ++ extra)
                     | none => .fail ⟨"invalid hex digit in \\u escape", pos⟩) := rfl
              rw [hL] at h
              rw [hR]
              cases hh : hex4 a b c2 d with
              | none => rw [hh] at h; simp at h
              | some cp =>
                  rw [hh] at h
                  exact strLitEmitAt_local cp pos 6 t3 extra c w rest h
        by_cases heU : e = 'U'
        · subst heU
          match t2 with
          | [] => exact (failNotEmit ⟨_, rfl⟩ h).elim
          | [_] => exact (failNotEmit ⟨_, rfl⟩ h).elim
          | [_, _] => exact (failNotEmit ⟨_, rfl⟩ h).elim
          | [_, _, _] => exact (failNotEmit ⟨_, rfl⟩ h).elim
          | [_, _, _, _] => exact (failNotEmit ⟨_, rfl⟩ h).elim
          | [_, _, _, _, _] => exact (failNotEmit ⟨_, rfl⟩ h).elim
          | [_, _, _, _, _, _] => exact (failNotEmit ⟨_, rfl⟩ h).elim
          | [_, _, _, _, _, _, _] => exact (failNotEmit ⟨_, rfl⟩ h).elim
          | a :: b :: c2 :: d :: e4 :: f :: g :: i :: t3 =>
              have hL : strLitNextStep pos
                    ('\\' :: 'U' :: a :: b :: c2 :: d :: e4 :: f :: g :: i :: t3)
                  = (match hex8 a b c2 d e4 f g i with
                     | some cp => strLitEmitAt cp pos 10 t3
                     | none => .fail ⟨"invalid hex digit in \\U escape", pos⟩) := rfl
              have hR : strLitNextStep pos
                    (('\\' :: 'U' :: a :: b :: c2 :: d :: e4 :: f :: g :: i :: t3) ++ extra)
                  = (match hex8 a b c2 d e4 f g i with
                     | some cp => strLitEmitAt cp pos 10 (t3 ++ extra)
                     | none => .fail ⟨"invalid hex digit in \\U escape", pos⟩) := rfl
              rw [hL] at h
              rw [hR]
              cases hh : hex8 a b c2 d e4 f g i with
              | none => rw [hh] at h; simp at h
              | some cp =>
                  rw [hh] at h
                  exact strLitEmitAt_local cp pos 10 t3 extra c w rest h
        · rw [strLitNextStep_badEscape pos e t2 het heb hen her hef hedq hesq hebs heu heU] at h
          simp at h
    · rw [strLitNextStep_plain pos c0 t hq hbs hnl hcr] at h
      injection h with e1 e2 e3
      subst e1; subst e2; subst e3
      rw [List.cons_append, strLitNextStep_plain pos c0 (t ++ extra) hq hbs hnl hcr]

/-! ## The close arm

`strLitNextStep` closes only on a literal `"`, so the close arm needs no
side condition: the character that ends the run is present in the input,
not discovered by running out of it. -/

theorem strLitEmitAt_ne_close (cp pos width : Nat) (rest r : List Char) :
    strLitEmitAt cp pos width rest ≠ .close r := by
  unfold strLitEmitAt; split <;> simp

set_option maxHeartbeats 4000000 in
theorem strLitNextStep_close_local (pos : Nat) (cs extra rest : List Char)
    (h : strLitNextStep pos cs = .close rest) :
    strLitNextStep pos (cs ++ extra) = .close (rest ++ extra) := by
  unfold strLitNextStep at h ⊢
  split at h <;> (try split at h) <;> simp_all [strLitEmitAt_ne_close]

/-! ## The body reader

Fuel-parameter induction, because the recursion is well-founded on
`cs.length` rather than structural. -/

theorem readStringLiteralBody_local : ∀ (n : Nat) (cs : List Char), cs.length ≤ n →
    ∀ (pos : Nat) (extra : List Char) (s : String) (p' : Nat) (rest : List Char),
    readStringLiteralBody pos cs = .ok (s, p', rest) →
    readStringLiteralBody pos (cs ++ extra) = .ok (s, p', rest ++ extra)
  | 0, cs, hn, pos, extra, s, p', rest, h => by
      have hcs : cs = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hcs
      rw [readStringLiteralBody_fail pos [] _ rfl] at h
      simp at h
  | n + 1, cs, hn, pos, extra, s, p', rest, h => by
      cases hstep : strLitNextStep pos cs with
      | fail e => rw [readStringLiteralBody_fail pos cs e hstep] at h; simp at h
      | close r =>
          rw [readStringLiteralBody_close pos cs r hstep] at h
          simp at h
          obtain ⟨h1, h2, h3⟩ := h
          subst h1; subst h2; subst h3
          rw [readStringLiteralBody_close pos (cs ++ extra) (r ++ extra)
                (strLitNextStep_close_local pos cs extra r hstep)]
      | emit c w r =>
          have hshort : r.length < cs.length := strLitNextStep_emit_shorter hstep
          rw [readStringLiteralBody_emit pos cs r c w hstep] at h
          cases hrec : readStringLiteralBody (pos + w) r with
          | error e => rw [hrec] at h; simp [Except.map] at h
          | ok v =>
              obtain ⟨s2, p2, r2⟩ := v
              rw [readStringLiteralBody_emit pos (cs ++ extra) (r ++ extra) c w
                    (strLitNextStep_emit_local pos cs extra r c w hstep),
                  readStringLiteralBody_local n r (by omega) (pos + w) extra s2 p2 r2 hrec]
              rw [hrec] at h
              simp [Except.map] at h ⊢
              obtain ⟨h1, h2, h3⟩ := h
              subst h1; subst h2; subst h3
              simp

/-- The quoted literal, opening delimiter included. -/
theorem readStringLiteralQuoted_local (pos : Nat) (cs extra : List Char)
    (s : String) (p' : Nat) (rest : List Char)
    (h : readStringLiteralQuoted pos cs = .ok (s, p', rest)) :
    readStringLiteralQuoted pos (cs ++ extra) = .ok (s, p', rest ++ extra) := by
  cases cs with
  | nil => simp [readStringLiteralQuoted] at h
  | cons c0 r0 =>
      by_cases hq : c0 = '"'
      · subst hq
        simp only [readStringLiteralQuoted, List.cons_append] at h ⊢
        exact readStringLiteralBody_local r0.length r0 (by omega) (pos + 1) extra
          s p' rest h
      · simp [readStringLiteralQuoted, hq] at h

/-! ## The language-tag run -/

/-- ⚠️ The language-tag run uses a span, so it carries the same
stopped-inside condition the blank-node reader does. -/
theorem readLangTagRun_local (pos : Nat) (cs extra : List Char) (a : Char)
    (t : List Char) (h : (cs.span isLangChar).2 = a :: t) :
    readLangTagRun pos (cs ++ extra)
      = ((readLangTagRun pos cs).1, (readLangTagRun pos cs).2.1,
         (readLangTagRun pos cs).2.2 ++ extra) := by
  simp only [readLangTagRun]
  cases hsp : cs.span isLangChar with
  | mk taken dropped =>
      rw [hsp] at h
      subst h
      rw [span_append_of_stopped isLangChar cs taken a t extra hsp]
      simp

/-! ## Axiom audit -/

#print axioms strLitNextStep_emit_local
#print axioms strLitNextStep_close_local
#print axioms readStringLiteralBody_local
#print axioms readStringLiteralQuoted_local
#print axioms readLangTagRun_local

end L4Factoidal.Syntax
