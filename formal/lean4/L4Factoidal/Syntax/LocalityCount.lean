/-
L4Factoidal.Syntax.LocalityCount — positions count characters.

Every reader's returned position is its starting position plus the
number of characters it took. Stated as
`p' + rest.length = pos + cs.length`, which keeps `omega` in play by
avoiding subtraction.

This is what makes the streaming module's threaded offset CORRECT
rather than merely plausible: `feedChunk` advances its stored offset by
`complete.length`, and these theorems are what say the parser's own
position advanced by exactly that much. Without them the stored offset
would be an assumption, and a parse error in a later chunk could name
the wrong place.

It is also the Lean counterpart of the F\* module's `lemma_*_shift`
family, in the sense that both exist so a restart can be lined up with
a run that never stopped — but the F\* version has to shift byte offsets
through `Parser.FastString`, while here the position is a plain
character count over a `List Char`.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.Syntax.LocalitySkips

namespace L4Factoidal.Syntax
open L4Factoidal.RDF

/-! ## Steps count what they consume -/

theorem iriNextStep_emit_count {pos : Nat} {cs : List Char} {c : Char} {w : Nat}
    {rest : List Char} (h : iriNextStep pos cs = .emit c w rest) :
    rest.length + w = cs.length := by
  unfold iriNextStep at h
  split at h <;> (try split at h) <;>
    first
      | (rw [iriEmitAt_emit h, iriEmitAt_emit_width h]; simp <;> omega)
      | (obtain ⟨_, hw, hr⟩ := h; subst hw; subst hr; simp)
      | (simp_all; done)
      | (grind; done)

theorem iriNextStep_close_count {pos : Nat} {cs rest : List Char}
    (h : iriNextStep pos cs = .close rest) : rest.length + 1 = cs.length := by
  unfold iriNextStep at h
  split at h <;> (try split at h) <;> simp_all [iriEmitAt_ne_close]

theorem strLitNextStep_emit_count {pos : Nat} {cs : List Char} {c : Char} {w : Nat}
    {rest : List Char} (h : strLitNextStep pos cs = .emit c w rest) :
    rest.length + w = cs.length := by
  unfold strLitNextStep at h
  split at h <;> (try split at h) <;>
    first
      | (rw [strLitEmitAt_emit h, strLitEmitAt_emit_width h]; simp <;> omega)
      | (obtain ⟨_, hw, hr⟩ := h; subst hw; subst hr; simp)
      | (simp_all; done)
      | (grind; done)

theorem strLitNextStep_close_count {pos : Nat} {cs rest : List Char}
    (h : strLitNextStep pos cs = .close rest) : rest.length + 1 = cs.length := by
  unfold strLitNextStep at h
  split at h <;> (try split at h) <;> simp_all [strLitEmitAt_ne_close]

/-! ## Skips count what they consume -/

theorem skipWs_counts (pos : Nat) (cs : List Char) :
    (skipWs pos cs).1 + (skipWs pos cs).2.length = pos + cs.length := by
  simp only [skipWs]
  have hl := congrArg List.length (span_append isNtWs cs)
  simp only [List.length_append] at hl
  omega

theorem skipToEol_counts : ∀ (pos : Nat) (cs : List Char),
    (skipToEol pos cs).1 + (skipToEol pos cs).2.length = pos + cs.length
  | pos, [] => by simp [skipToEol]
  | pos, c :: t => by
      by_cases hn : c = '\n'
      · subst hn; simp [skipToEol]
      · by_cases hr : c = '\r'
        · subst hr; simp [skipToEol]
        · have h1 : skipToEol pos (c :: t) = skipToEol (pos + 1) t := by
            simp [skipToEol, hn, hr]
          rw [h1]
          have := skipToEol_counts (pos + 1) t
          simp <;> omega

theorem skipComment_counts (pos : Nat) (cs : List Char) :
    (skipComment pos cs).1 + (skipComment pos cs).2.length = pos + cs.length := by
  cases cs with
  | nil => simp [skipComment]
  | cons c t =>
      by_cases hc : c = '#'
      · subst hc
        have h1 : skipComment pos ('#' :: t) = skipToEol (pos + 1) t := rfl
        rw [h1]
        have := skipToEol_counts (pos + 1) t
        simp <;> omega
      · simp [skipComment, hc]

theorem skipEol_counts (pos : Nat) (cs : List Char) :
    (skipEol pos cs).1 + (skipEol pos cs).2.length = pos + cs.length := by
  cases cs with
  | nil => simp [skipEol]
  | cons c t =>
    by_cases hr : c = '\r'
    · subst hr
      cases t with
      | nil => have h1 : skipEol pos ['\r'] = (pos + 1, []) := rfl
               rw [h1]; simp <;> omega
      | cons b t2 =>
        by_cases hb : b = '\n'
        · subst hb
          have h1 : skipEol pos ('\r' :: '\n' :: t2) = (pos + 2, t2) := rfl
          rw [h1]; simp <;> omega
        · have h1 : skipEol pos ('\r' :: b :: t2) = (pos + 1, b :: t2) := by
            simp [skipEol, hb]
          rw [h1]; simp <;> omega
    · by_cases hn : c = '\n'
      · subst hn
        have h1 : skipEol pos ('\n' :: t) = (pos + 1, t) := rfl
        rw [h1]; simp <;> omega
      · have h1 : skipEol pos (c :: t) = (pos, c :: t) := by simp [skipEol, hr, hn]
        rw [h1]


/-! ## Readers count what they consume

Every reader's returned position is its starting position plus the
number of characters it took. Stated as `p' + rest.length = pos +
cs.length`, which avoids subtraction and keeps `omega` in play. -/

theorem readIriRefBody_counts : ∀ (n : Nat) (cs : List Char), cs.length ≤ n →
    ∀ (pos : Nat) (s : String) (p' : Nat) (rest : List Char),
    readIriRefBody pos cs = .ok (s, p', rest) → p' + rest.length = pos + cs.length
  | 0, cs, hn, pos, s, p', rest, h => by
      have hcs : cs = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hcs
      rw [readIriRefBody_fail_eq pos [] _ rfl] at h
      simp at h
  | n + 1, cs, hn, pos, s, p', rest, h => by
      cases hstep : iriNextStep pos cs with
      | fail e => rw [readIriRefBody_fail_eq pos cs e hstep] at h; simp at h
      | close r =>
          rw [readIriRefBody_close_eq pos cs r hstep] at h
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          have hc := iriNextStep_close_count hstep
          have h1 : p' = pos + 1 := by grind
          have h2 : rest = r := by grind
          subst h1; subst h2; omega
      | emit c w r =>
          have hshort : r.length < cs.length := iriNextStep_emit_shorter hstep
          have hcnt := iriNextStep_emit_count hstep
          rw [readIriRefBody_emit_eq pos cs r c w hstep] at h
          cases hrec : readIriRefBody (pos + w) r with
          | error e => rw [hrec] at h; simp [Except.map] at h
          | ok v =>
              obtain ⟨s2, p2, r2⟩ := v
              rw [hrec] at h
              simp [Except.map] at h
              have hp : p' = p2 := by grind
              have hr : rest = r2 := by grind
              subst hp; subst hr
              have := readIriRefBody_counts n r (by omega) (pos + w) s2 p' rest hrec
              omega

theorem readIriRef_counts (pos : Nat) (cs : List Char) (s : String) (p' : Nat)
    (rest : List Char) (h : readIriRef pos cs = .ok (s, p', rest)) :
    p' + rest.length = pos + cs.length := by
  cases cs with
  | nil => simp [readIriRef] at h
  | cons c0 r0 =>
      by_cases hlt : c0 = '<'
      · subst hlt
        simp only [readIriRef] at h
        have := readIriRefBody_counts r0.length r0 (by omega) (pos + 1) s p' rest h
        simp
        omega
      · simp [readIriRef, hlt] at h

theorem readStringLiteralBody_counts : ∀ (n : Nat) (cs : List Char), cs.length ≤ n →
    ∀ (pos : Nat) (s : String) (p' : Nat) (rest : List Char),
    readStringLiteralBody pos cs = .ok (s, p', rest) → p' + rest.length = pos + cs.length
  | 0, cs, hn, pos, s, p', rest, h => by
      have hcs : cs = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hcs
      rw [readStringLiteralBody_fail pos [] _ rfl] at h
      simp at h
  | n + 1, cs, hn, pos, s, p', rest, h => by
      cases hstep : strLitNextStep pos cs with
      | fail e => rw [readStringLiteralBody_fail pos cs e hstep] at h; simp at h
      | close r =>
          rw [readStringLiteralBody_close pos cs r hstep] at h
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          have hc := strLitNextStep_close_count hstep
          have h1 : p' = pos + 1 := by grind
          have h2 : rest = r := by grind
          subst h1; subst h2; omega
      | emit c w r =>
          have hshort : r.length < cs.length := strLitNextStep_emit_shorter hstep
          have hcnt := strLitNextStep_emit_count hstep
          rw [readStringLiteralBody_emit pos cs r c w hstep] at h
          cases hrec : readStringLiteralBody (pos + w) r with
          | error e => rw [hrec] at h; simp [Except.map] at h
          | ok v =>
              obtain ⟨s2, p2, r2⟩ := v
              rw [hrec] at h
              simp [Except.map] at h
              have hp : p' = p2 := by grind
              have hr : rest = r2 := by grind
              subst hp; subst hr
              have := readStringLiteralBody_counts n r (by omega) (pos + w) s2 p' rest hrec
              omega

theorem readStringLiteralQuoted_counts (pos : Nat) (cs : List Char) (s : String)
    (p' : Nat) (rest : List Char)
    (h : readStringLiteralQuoted pos cs = .ok (s, p', rest)) :
    p' + rest.length = pos + cs.length := by
  cases cs with
  | nil => simp [readStringLiteralQuoted] at h
  | cons c0 r0 =>
      by_cases hq : c0 = '"'
      · subst hq
        simp only [readStringLiteralQuoted] at h
        have := readStringLiteralBody_counts r0.length r0 (by omega) (pos + 1) s p' rest h
        simp
        omega
      · simp [readStringLiteralQuoted, hq] at h


theorem readBlankNodeLabel_counts (pos : Nat) (cs : List Char) (s : String) (p' : Nat)
    (rest : List Char) (h : readBlankNodeLabel pos cs = .ok (s, p', rest)) :
    p' + rest.length = pos + cs.length := by
  cases cs with
  | nil => simp [readBlankNodeLabel] at h
  | cons a0 r0 =>
    by_cases hu : a0 = '_'
    · subst hu
      cases r0 with
      | nil => simp [readBlankNodeLabel] at h
      | cons a1 r1 =>
        by_cases hco : a1 = ':'
        · subst hco
          cases r1 with
          | nil => simp [readBlankNodeLabel] at h
          | cons c0 t =>
            simp only [readBlankNodeLabel] at h
            split at h
            · simp at h
            · cases hsp : t.span isBnodeChar with
              | mk taken dropped =>
                rw [hsp] at h
                simp only at h
                have hta : taken ++ dropped = t := by
                  have := span_append isBnodeChar t
                  rw [hsp] at this; exact this
                have hlen : taken.length + dropped.length = t.length := by
                  have := congrArg List.length hta
                  simpa using this
                split at h
                · simp only [Except.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨_, hp, hr⟩ := h
                  subst hp; subst hr
                  simp [List.length_dropLast]
                  omega
                · simp only [Except.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨_, hp, hr⟩ := h
                  subst hp; subst hr
                  simp
                  omega
        · simp [readBlankNodeLabel, hco] at h
    · simp [readBlankNodeLabel, hu] at h

theorem readLangTag_counts (pos : Nat) (cs : List Char) (str : String) (p' : Nat)
    (rest : List Char) (h : readLangTag pos cs = .ok (str, p', rest)) :
    p' + rest.length = pos + cs.length := by
  cases cs with
  | nil => simp [readLangTag] at h
  | cons c0 t =>
    by_cases ha : c0 = '@'
    · subst ha
      cases t with
      | nil => simp [readLangTag] at h
      | cons c1 t2 =>
        simp only [readLangTag] at h
        cases hst : isLangStart c1 with
        | false => simp [hst] at h
        | true =>
          simp only [hst, Bool.not_true, Bool.false_eq_true, if_neg,
                     not_false_eq_true] at h
          cases hsp : (c1 :: t2).span isLangChar with
          | mk taken dropped =>
            have hta : taken ++ dropped = c1 :: t2 := by
              have := span_append isLangChar (c1 :: t2)
              rw [hsp] at this; exact this
            have hlen : taken.length + dropped.length = t2.length + 1 := by
              have := congrArg List.length hta
              simpa using this
            have hEq : readLangTagRun (pos + 1) (c1 :: t2)
                = (String.ofList taken, pos + 1 + taken.length, dropped) := by
              simp [readLangTagRun, hsp]
            rw [hEq] at h
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨_, hp, hr⟩ := h
            subst hp; subst hr
            simp
            omega
    · simp [readLangTag, ha] at h

theorem readDatatype_counts (pos : Nat) (cs : List Char) (wi : WfIri) (p' : Nat)
    (rest : List Char) (h : readDatatype pos cs = .ok (wi, p', rest)) :
    p' + rest.length = pos + cs.length := by
  cases cs with
  | nil => simp [readDatatype] at h
  | cons c0 t =>
    by_cases h0 : c0 = '^'
    · subst h0
      cases t with
      | nil => simp [readDatatype] at h
      | cons c1 t2 =>
        by_cases h1 : c1 = '^'
        · subst h1
          simp only [readDatatype] at h
          cases hr : readIriRef (pos + 2) t2 with
          | error e => rw [hr] at h; simp at h
          | ok v =>
              obtain ⟨iriStr, pos2, rest2⟩ := v
              have hc := readIriRef_counts (pos + 2) t2 iriStr pos2 rest2 hr
              rw [hr] at h
              simp only at h
              cases hm : mkIri pos iriStr with
              | error e => simp_all
              | ok wi2 =>
                  rw [hm] at h
                  simp only [Except.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨_, hp, hr⟩ := h
                  subst hp; subst hr
                  simp
                  omega
        · simp [readDatatype, h1] at h
    · simp [readDatatype, h0] at h

theorem readLiteral11_counts (pos : Nat) (cs : List Char) (wl : WfLiteral) (p' : Nat)
    (rest : List Char) (h : readLiteral .rdf11 pos cs = .ok (wl, p', rest)) :
    p' + rest.length = pos + cs.length := by
  simp only [readLiteral] at h
  cases hq : readStringLiteralQuoted pos cs with
  | error e => rw [hq] at h; simp at h
  | ok v =>
      obtain ⟨lex, pos1, r1⟩ := v
      have hbase := readStringLiteralQuoted_counts pos cs lex pos1 r1 hq
      rw [hq] at h
      simp only at h
      have hlang : ∀ (tg : String) (p2 : Nat) (r2 : List Char),
          readLangTag pos1 r1 = .ok (tg, p2, r2) → p2 + r2.length = pos + cs.length :=
        fun tg p2 r2 he => by have := readLangTag_counts _ _ _ _ _ he; omega
      have hdt : ∀ (d : WfIri) (p2 : Nat) (r2 : List Char),
          readDatatype pos1 r1 = .ok (d, p2, r2) → p2 + r2.length = pos + cs.length :=
        fun d p2 r2 he => by have := readDatatype_counts _ _ _ _ _ he; omega
      split at h <;> (try split at h) <;> (try split at h) <;> (grind; done)

theorem readSubject_counts (pos : Nat) (cs : List Char) (subj : Subject) (p' : Nat)
    (rest : List Char) (h : readSubject pos cs = .ok (subj, p', rest)) :
    p' + rest.length = pos + cs.length := by
  have hi : ∀ (str : String) (p2 : Nat) (r2 : List Char),
      readIriRef pos cs = .ok (str, p2, r2) → p2 + r2.length = pos + cs.length :=
    fun str p2 r2 he => readIriRef_counts _ _ _ _ _ he
  have hb : ∀ (lab : String) (p2 : Nat) (r2 : List Char),
      readBlankNodeLabel pos cs = .ok (lab, p2, r2) → p2 + r2.length = pos + cs.length :=
    fun lab p2 r2 he => readBlankNodeLabel_counts _ _ _ _ _ he
  simp only [readSubject] at h
  split at h <;> (try split at h) <;> (try split at h) <;> (grind; done)

theorem readPredicate_counts (pos : Nat) (cs : List Char) (pred : WfIri) (p' : Nat)
    (rest : List Char) (h : readPredicate pos cs = .ok (pred, p', rest)) :
    p' + rest.length = pos + cs.length := by
  have hi : ∀ (str : String) (p2 : Nat) (r2 : List Char),
      readIriRef pos cs = .ok (str, p2, r2) → p2 + r2.length = pos + cs.length :=
    fun str p2 r2 he => readIriRef_counts _ _ _ _ _ he
  simp only [readPredicate] at h
  split at h <;> (try split at h) <;> (grind; done)

theorem readObject11_counts (pos : Nat) (cs : List Char) (obj : Term) (p' : Nat)
    (rest : List Char) (h : readObject11 pos cs = .ok (obj, p', rest)) :
    p' + rest.length = pos + cs.length := by
  have hi : ∀ (str : String) (p2 : Nat) (r2 : List Char),
      readIriRef pos cs = .ok (str, p2, r2) → p2 + r2.length = pos + cs.length :=
    fun str p2 r2 he => readIriRef_counts _ _ _ _ _ he
  have hb : ∀ (lab : String) (p2 : Nat) (r2 : List Char),
      readBlankNodeLabel pos cs = .ok (lab, p2, r2) → p2 + r2.length = pos + cs.length :=
    fun lab p2 r2 he => readBlankNodeLabel_counts _ _ _ _ _ he
  have hl : ∀ (li : WfLiteral) (p2 : Nat) (r2 : List Char),
      readLiteral .rdf11 pos cs = .ok (li, p2, r2) → p2 + r2.length = pos + cs.length :=
    fun li p2 r2 he => readLiteral11_counts _ _ _ _ _ he
  simp only [readObject11] at h
  split at h <;> (try split at h) <;> (try split at h) <;> (grind; done)

theorem readGraphLabel_counts (pos : Nat) (cs : List Char) (g : Subject) (p' : Nat)
    (rest : List Char) (h : readGraphLabel pos cs = .ok (g, p', rest)) :
    p' + rest.length = pos + cs.length := by
  have hi : ∀ (str : String) (p2 : Nat) (r2 : List Char),
      readIriRef pos cs = .ok (str, p2, r2) → p2 + r2.length = pos + cs.length :=
    fun str p2 r2 he => readIriRef_counts _ _ _ _ _ he
  have hb : ∀ (lab : String) (p2 : Nat) (r2 : List Char),
      readBlankNodeLabel pos cs = .ok (lab, p2, r2) → p2 + r2.length = pos + cs.length :=
    fun lab p2 r2 he => readBlankNodeLabel_counts _ _ _ _ _ he
  simp only [readGraphLabel] at h
  split at h <;> (try split at h) <;> (try split at h) <;> (grind; done)

theorem readOptGraphLabel_counts (pos : Nat) (cs : List Char) (gopt : Option Subject)
    (p' : Nat) (rest : List Char)
    (h : readOptGraphLabel pos cs = .ok (gopt, p', rest)) :
    p' + rest.length = pos + cs.length := by
  have hw := skipWs_counts pos cs
  have hg : ∀ (g : Subject) (p2 : Nat) (r2 : List Char),
      readGraphLabel (skipWs pos cs).1 (skipWs pos cs).2 = .ok (g, p2, r2) →
      p2 + r2.length = pos + cs.length :=
    fun g p2 r2 he => by have := readGraphLabel_counts _ _ _ _ _ he; omega
  simp only [readOptGraphLabel] at h
  split at h <;> (try split at h) <;> (grind; done)

theorem readNQuad11_counts (pos : Nat) (cs : List Char) (tr : Triple)
    (g : Option Subject) (p' : Nat) (rest : List Char)
    (h : readNQuad11 pos cs = .ok (tr, g, p', rest)) :
    p' + rest.length = pos + cs.length := by
  simp only [readNQuad11] at h
  cases hw1 : skipWs pos cs with
  | mk pos1 cs1 =>
    have s1 := skipWs_counts pos cs
    rw [hw1] at s1 h
    simp only at s1 h
    cases hs : readSubject pos1 cs1 with
    | error e => rw [hs] at h; simp at h
    | ok v1 =>
      obtain ⟨subj, pos2, cs2⟩ := v1
      have s2 := readSubject_counts pos1 cs1 subj pos2 cs2 hs
      rw [hs] at h; simp only at h
      cases hw2 : skipWs pos2 cs2 with
      | mk pos3 cs3 =>
        have s3 := skipWs_counts pos2 cs2
        rw [hw2] at s3 h
        simp only at s3 h
        cases hp : readPredicate pos3 cs3 with
        | error e => rw [hp] at h; simp at h
        | ok v2 =>
          obtain ⟨pred, pos4, cs4⟩ := v2
          have s4 := readPredicate_counts pos3 cs3 pred pos4 cs4 hp
          rw [hp] at h; simp only at h
          cases hw3 : skipWs pos4 cs4 with
          | mk pos5 cs5 =>
            have s5 := skipWs_counts pos4 cs4
            rw [hw3] at s5 h
            simp only at s5 h
            cases ho : readObject11 pos5 cs5 with
            | error e => rw [ho] at h; simp at h
            | ok v3 =>
              obtain ⟨obj, pos6, cs6⟩ := v3
              have s6 := readObject11_counts pos5 cs5 obj pos6 cs6 ho
              rw [ho] at h; simp only at h
              cases hgl : readOptGraphLabel pos6 cs6 with
              | error e => rw [hgl] at h; simp at h
              | ok v4 =>
                obtain ⟨gopt, pos7, cs7⟩ := v4
                have s7 := readOptGraphLabel_counts pos6 cs6 gopt pos7 cs7 hgl
                rw [hgl] at h; simp only at h
                cases hw4 : skipWs pos7 cs7 with
                | mk pos8 cs8 =>
                  have s8 := skipWs_counts pos7 cs7
                  rw [hw4] at s8 h
                  simp only at s8 h
                  cases hc8 : cs8 with
                  | nil => rw [hc8] at h; simp at h
                  | cons d cs9 =>
                    rw [hc8] at h s8
                    by_cases hd : d = '.'
                    · subst hd
                      simp only [Except.ok.injEq, Prod.mk.injEq] at h
                      simp at s8
                      grind
                    · simp [hd] at h

#print axioms readBlankNodeLabel_counts
#print axioms readLangTag_counts
#print axioms readDatatype_counts
#print axioms readLiteral11_counts
#print axioms readSubject_counts
#print axioms readObject11_counts
#print axioms readOptGraphLabel_counts
#print axioms readNQuad11_counts

#print axioms readIriRef_counts
#print axioms readStringLiteralQuoted_counts

#print axioms iriNextStep_emit_count
#print axioms strLitNextStep_emit_count
#print axioms skipWs_counts
#print axioms skipToEol_counts
#print axioms skipComment_counts
#print axioms skipEol_counts

end L4Factoidal.Syntax
