/-
L4Factoidal.Syntax.LocalitySuffix — every reader hands back a SUFFIX of
its input.

`Syntax.Locality`, `Syntax.LocalityLiteral` and `Syntax.LocalityLine`
say a reader answers the same on longer input. This module says where
the answer sits: the remainder a reader returns is a suffix of what it
was given, and `readNQuad11_dot` says more — the statement's terminating
`.` is still findable in the input, immediately before the remainder.

That last one is what the streaming fold needs. A chunk is cut after its
last newline, so the text handed to the parser ends with `'\n'`. If a
statement's remainder were empty, the input would end with the `.`
instead, and `readNQuad11_dot` is what refutes that. Without it the
per-line locality theorem cannot be applied, because its side condition
is exactly "the remainder is not empty".

The step functions do the work: every arm of `iriNextStep` and
`strLitNextStep` consumes a prefix of FIXED length, so the remainder is
`cs.drop w`, and a drop is a suffix. `iriNextStep_emit_drop` and
`strLitNextStep_emit_drop` state that; the rest is transitivity.

⚠️ The blank-node reader is the one place the suffix is not immediate.
Its trailing-dot branch hands back `'.' :: afterBody`, and that dot came
out of the LABEL, not out of the input at that position — so the proof
has to find it again, by splitting the label at its last character.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.Syntax.LocalityLine

namespace L4Factoidal.Syntax
open L4Factoidal.RDF

/-! ## Spans -/

theorem spanLoop_append {α : Type} (p : α → Bool) :
    ∀ (l acc : List α),
      (List.span.loop p l acc).1 ++ (List.span.loop p l acc).2 = acc.reverse ++ l
  | [], acc => by simp [List.span.loop]
  | c :: t, acc => by
      simp only [List.span.loop]
      by_cases hp : p c
      · simp only [hp, if_pos]
        rw [spanLoop_append p t (c :: acc)]
        simp
      · simp [hp]

theorem span_append {α : Type} (p : α → Bool) (l : List α) :
    (l.span p).1 ++ (l.span p).2 = l := by
  have h := spanLoop_append p l []
  simp only [List.reverse_nil, List.nil_append] at h
  exact h

theorem span_snd_suffix {α : Type} (p : α → Bool) (l : List α) :
    (l.span p).2 <:+ l := ⟨(l.span p).1, span_append p l⟩

/-! ## Skips -/

theorem skipWs_suffix (pos : Nat) (cs : List Char) : (skipWs pos cs).2 <:+ cs :=
  span_snd_suffix isNtWs cs

theorem skipToEol_suffix : ∀ (pos : Nat) (cs : List Char), (skipToEol pos cs).2 <:+ cs
  | pos, [] => by simp [skipToEol]
  | pos, c :: t => by
      by_cases hn : c = '\n'
      · subst hn; simp [skipToEol]
      · by_cases hr : c = '\r'
        · subst hr; simp [skipToEol]
        · have he : skipToEol pos (c :: t) = skipToEol (pos + 1) t := by
            simp [skipToEol, hn, hr]
          rw [he]
          exact (skipToEol_suffix (pos + 1) t).trans (List.suffix_cons c t)

theorem skipComment_suffix (pos : Nat) (cs : List Char) :
    (skipComment pos cs).2 <:+ cs := by
  cases cs with
  | nil => simp [skipComment]
  | cons c t =>
      by_cases hc : c = '#'
      · subst hc
        have he : skipComment pos ('#' :: t) = skipToEol (pos + 1) t := rfl
        rw [he]
        exact (skipToEol_suffix (pos + 1) t).trans (List.suffix_cons '#' t)
      · simp [skipComment, hc]

theorem skipEol_suffix (pos : Nat) (cs : List Char) : (skipEol pos cs).2 <:+ cs := by
  cases cs with
  | nil => simp [skipEol]
  | cons c t =>
    by_cases hr : c = '\r'
    · subst hr
      cases t with
      | nil =>
          have he : skipEol pos ['\r'] = (pos + 1, []) := rfl
          rw [he]; simp
      | cons b t2 =>
        by_cases hb : b = '\n'
        · subst hb
          have he : skipEol pos ('\r' :: '\n' :: t2) = (pos + 2, t2) := rfl
          rw [he]
          exact (List.suffix_cons '\n' t2).trans (List.suffix_cons '\r' ('\n' :: t2))
        · have he : skipEol pos ('\r' :: b :: t2) = (pos + 1, b :: t2) := by
            simp [skipEol, hb]
          rw [he]
          exact List.suffix_cons '\r' (b :: t2)
    · by_cases hn : c = '\n'
      · subst hn
        have he : skipEol pos ('\n' :: t) = (pos + 1, t) := rfl
        rw [he]
        exact List.suffix_cons '\n' t
      · have he : skipEol pos (c :: t) = (pos, c :: t) := by
          simp [skipEol, hr, hn]
        rw [he]
        simp

/-! ## The IRIREF reader

A step consumes a FIXED prefix, so its remainder is `cs.drop w`, and a
drop is a suffix. -/

theorem iriEmitAt_emit_width {cp pos width : Nat} {rest : List Char} {which : String}
    {c : Char} {w : Nat} {r : List Char}
    (h : iriEmitAt cp pos width rest which = .emit c w r) : w = width := by
  unfold iriEmitAt at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · simp only [IriStep.emit.injEq] at h; exact h.2.1.symm

theorem iriNextStep_close_drop {pos : Nat} {cs rest : List Char}
    (h : iriNextStep pos cs = .close rest) : rest = cs.drop 1 := by
  unfold iriNextStep at h
  split at h <;> (try split at h) <;> simp_all [iriEmitAt_ne_close]

theorem iriNextStep_emit_drop {pos : Nat} {cs : List Char} {c : Char} {w : Nat}
    {rest : List Char} (h : iriNextStep pos cs = .emit c w rest) : rest = cs.drop w := by
  unfold iriNextStep at h
  split at h <;> (try split at h) <;>
    first
      | (rw [iriEmitAt_emit h, iriEmitAt_emit_width h]; rfl)
      | (obtain ⟨_, hw, hr⟩ := h; subst hw; subst hr; simp)
      | (simp_all; done)
      | (grind; done)

theorem readIriRefBody_suffix : ∀ (n : Nat) (cs : List Char), cs.length ≤ n →
    ∀ (pos : Nat) (s : String) (p' : Nat) (rest : List Char),
    readIriRefBody pos cs = .ok (s, p', rest) → rest <:+ cs
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
          have : rest = r := by grind
          subst this
          rw [iriNextStep_close_drop hstep]
          exact List.drop_suffix 1 cs
      | emit c w r =>
          have hshort : r.length < cs.length := iriNextStep_emit_shorter hstep
          rw [readIriRefBody_emit_eq pos cs r c w hstep] at h
          cases hrec : readIriRefBody (pos + w) r with
          | error e => rw [hrec] at h; simp [Except.map] at h
          | ok v =>
              obtain ⟨s2, p2, r2⟩ := v
              rw [hrec] at h
              simp [Except.map] at h
              have hr : rest = r2 := by grind
              subst hr
              have hsub := readIriRefBody_suffix n r (by omega) (pos + w) s2 p2 rest hrec
              rw [iriNextStep_emit_drop hstep] at hsub
              exact hsub.trans (List.drop_suffix w cs)

theorem readIriRef_suffix (pos : Nat) (cs : List Char) (s : String) (p' : Nat)
    (rest : List Char) (h : readIriRef pos cs = .ok (s, p', rest)) : rest <:+ cs := by
  cases cs with
  | nil => simp [readIriRef] at h
  | cons c0 r0 =>
      by_cases hlt : c0 = '<'
      · subst hlt
        simp only [readIriRef] at h
        exact (readIriRefBody_suffix r0.length r0 (by omega) (pos + 1) s p' rest h).trans
          (List.suffix_cons '<' r0)
      · simp [readIriRef, hlt] at h


/-! ## Blank-node labels

The trailing-dot branch hands back `'.' :: afterBody`, so the dot has to
be found again inside the input. -/

theorem list_getLast?_split {α : Type} :
    ∀ (l : List α) (a : α), l.getLast? = some a → l = l.dropLast ++ [a]
  | [], a, h => by simp at h
  | [x], a, h => by simp at h; simp [h]
  | x :: y :: t, a, h => by
      simp only [List.getLast?_cons_cons] at h
      have ih := list_getLast?_split (y :: t) a h
      have hd : (x :: y :: t).dropLast = x :: (y :: t).dropLast := rfl
      rw [hd, List.cons_append, ← ih]

theorem readBlankNodeLabel_suffix (pos : Nat) (cs : List Char) (s : String) (p' : Nat)
    (rest : List Char) (h : readBlankNodeLabel pos cs = .ok (s, p', rest)) : rest <:+ cs := by
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
                have hsuf : dropped <:+ t := ⟨taken, hta⟩
                split at h
                · -- trailing dot: the remainder is '.' :: dropped
                  rename_i hlast
                  simp only [Except.ok.injEq, Prod.mk.injEq] at h
                  have hr : rest = '.' :: dropped := by grind
                  subst hr
                  cases htk : taken with
                  | nil =>
                      rw [htk] at hta hlast
                      simp at hlast hta
                      subst hlast
                      rw [← hta]
                      exact (List.suffix_cons ':' _).trans (List.suffix_cons '_' _)
                  | cons b tb =>
                      rw [htk] at hta hlast
                      simp only [List.getLast?_cons_cons] at hlast
                      have hsplit := list_getLast?_split (b :: tb) '.' hlast
                      have ht2 : (b :: tb).dropLast ++ ['.'] ++ dropped
                          = (b :: tb) ++ dropped := by rw [← hsplit]
                      have ht3 : (b :: tb).dropLast ++ ('.' :: dropped) = t := by
                        rw [← hta, ← ht2]
                        simp
                      have : ('.' :: dropped) <:+ t := ⟨(b :: tb).dropLast, ht3⟩
                      exact ((this.trans (List.suffix_cons c0 t)).trans
                        (List.suffix_cons ':' _)).trans (List.suffix_cons '_' _)
                · simp only [Except.ok.injEq, Prod.mk.injEq] at h
                  have hr : rest = dropped := by grind
                  subst hr
                  exact ((hsuf.trans (List.suffix_cons c0 t)).trans
                    (List.suffix_cons ':' _)).trans (List.suffix_cons '_' _)
        · simp [readBlankNodeLabel, hco] at h
    · simp [readBlankNodeLabel, hu] at h

/-! ## String literals -/

theorem strLitEmitAt_emit_width {cp pos width : Nat} {rest : List Char}
    {c : Char} {w : Nat} {r : List Char}
    (h : strLitEmitAt cp pos width rest = .emit c w r) : w = width := by
  unfold strLitEmitAt at h
  split at h
  · exact absurd h (by simp)
  · simp only [StrLitStep.emit.injEq] at h; exact h.2.1.symm

theorem strLitNextStep_close_drop {pos : Nat} {cs rest : List Char}
    (h : strLitNextStep pos cs = .close rest) : rest = cs.drop 1 := by
  unfold strLitNextStep at h
  split at h <;> (try split at h) <;> simp_all [strLitEmitAt_ne_close]

theorem strLitNextStep_emit_drop {pos : Nat} {cs : List Char} {c : Char} {w : Nat}
    {rest : List Char} (h : strLitNextStep pos cs = .emit c w rest) :
    rest = cs.drop w := by
  unfold strLitNextStep at h
  split at h <;> (try split at h) <;>
    first
      | (rw [strLitEmitAt_emit h, strLitEmitAt_emit_width h]; rfl)
      | (obtain ⟨_, hw, hr⟩ := h; subst hw; subst hr; simp)
      | (simp_all; done)
      | (grind; done)

theorem readStringLiteralBody_suffix : ∀ (n : Nat) (cs : List Char), cs.length ≤ n →
    ∀ (pos : Nat) (s : String) (p' : Nat) (rest : List Char),
    readStringLiteralBody pos cs = .ok (s, p', rest) → rest <:+ cs
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
          have hr : rest = r := by grind
          subst hr
          rw [strLitNextStep_close_drop hstep]
          exact List.drop_suffix 1 cs
      | emit c w r =>
          have hshort : r.length < cs.length := strLitNextStep_emit_shorter hstep
          rw [readStringLiteralBody_emit pos cs r c w hstep] at h
          cases hrec : readStringLiteralBody (pos + w) r with
          | error e => rw [hrec] at h; simp [Except.map] at h
          | ok v =>
              obtain ⟨s2, p2, r2⟩ := v
              rw [hrec] at h
              simp [Except.map] at h
              have hr : rest = r2 := by grind
              subst hr
              have hsub := readStringLiteralBody_suffix n r (by omega) (pos + w) s2 p2
                rest hrec
              rw [strLitNextStep_emit_drop hstep] at hsub
              exact hsub.trans (List.drop_suffix w cs)

theorem readStringLiteralQuoted_suffix (pos : Nat) (cs : List Char) (s : String)
    (p' : Nat) (rest : List Char)
    (h : readStringLiteralQuoted pos cs = .ok (s, p', rest)) : rest <:+ cs := by
  cases cs with
  | nil => simp [readStringLiteralQuoted] at h
  | cons c0 r0 =>
      by_cases hq : c0 = '"'
      · subst hq
        simp only [readStringLiteralQuoted] at h
        exact (readStringLiteralBody_suffix r0.length r0 (by omega) (pos + 1) s p'
          rest h).trans (List.suffix_cons '"' r0)
      · simp [readStringLiteralQuoted, hq] at h


/-! ## Language tags and datatypes -/

theorem readLangTag_suffix (pos : Nat) (cs : List Char) (str : String) (p' : Nat)
    (rest : List Char) (h : readLangTag pos cs = .ok (str, p', rest)) : rest <:+ cs := by
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
          have hEq : readLangTagRun (pos + 1) (c1 :: t2) = (str, p', rest) := by
            simpa using h
          have hspan : ((c1 :: t2).span isLangChar).2 = rest := by
            have : (readLangTagRun (pos + 1) (c1 :: t2)).2.2 = rest := by rw [hEq]
            simpa [readLangTagRun] using this
          have := span_snd_suffix isLangChar (c1 :: t2)
          rw [hspan] at this
          exact this.trans (List.suffix_cons '@' (c1 :: t2))
    · simp [readLangTag, ha] at h

theorem readDatatype_suffix (pos : Nat) (cs : List Char) (wi : WfIri) (p' : Nat)
    (rest : List Char) (h : readDatatype pos cs = .ok (wi, p', rest)) : rest <:+ cs := by
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
              rw [hr] at h
              simp only at h
              have hsub := readIriRef_suffix (pos + 2) t2 iriStr pos2 rest2 hr
              cases hm : mkIri pos iriStr with
              | error e => simp_all
              | ok wi2 =>
                  rw [hm] at h
                  simp only [Except.ok.injEq, Prod.mk.injEq] at h
                  have hrr : rest = rest2 := by grind
                  subst hrr
                  exact (hsub.trans (List.suffix_cons '^' t2)).trans
                    (List.suffix_cons '^' ('^' :: t2))
        · simp [readDatatype, h1] at h
    · simp [readDatatype, h0] at h

theorem readLiteral11_suffix (pos : Nat) (cs : List Char) (wl : WfLiteral) (p' : Nat)
    (rest : List Char) (h : readLiteral .rdf11 pos cs = .ok (wl, p', rest)) :
    rest <:+ cs := by
  simp only [readLiteral] at h
  cases hq : readStringLiteralQuoted pos cs with
  | error e => rw [hq] at h; simp at h
  | ok v =>
      obtain ⟨lex, pos1, r1⟩ := v
      have hbase := readStringLiteralQuoted_suffix pos cs lex pos1 r1 hq
      rw [hq] at h
      simp only at h
      have hlang : ∀ (tg : String) (p2 : Nat) (r2 : List Char),
          readLangTag pos1 r1 = .ok (tg, p2, r2) → r2 <:+ cs :=
        fun tg p2 r2 he => (readLangTag_suffix _ _ _ _ _ he).trans hbase
      have hdt : ∀ (d : WfIri) (p2 : Nat) (r2 : List Char),
          readDatatype pos1 r1 = .ok (d, p2, r2) → r2 <:+ cs :=
        fun d p2 r2 he => (readDatatype_suffix _ _ _ _ _ he).trans hbase
      split at h <;> (try split at h) <;> (try split at h) <;> (grind; done)


/-! ## Subject, predicate, object, graph label -/

theorem readSubject_suffix (pos : Nat) (cs : List Char) (subj : Subject) (p' : Nat)
    (rest : List Char) (h : readSubject pos cs = .ok (subj, p', rest)) : rest <:+ cs := by
  have hi : ∀ (str : String) (p2 : Nat) (r2 : List Char),
      readIriRef pos cs = .ok (str, p2, r2) → r2 <:+ cs :=
    fun str p2 r2 he => readIriRef_suffix _ _ _ _ _ he
  have hb : ∀ (lab : String) (p2 : Nat) (r2 : List Char),
      readBlankNodeLabel pos cs = .ok (lab, p2, r2) → r2 <:+ cs :=
    fun lab p2 r2 he => readBlankNodeLabel_suffix _ _ _ _ _ he
  simp only [readSubject] at h
  split at h <;> (try split at h) <;> (try split at h) <;> (grind; done)

theorem readPredicate_suffix (pos : Nat) (cs : List Char) (pred : WfIri) (p' : Nat)
    (rest : List Char) (h : readPredicate pos cs = .ok (pred, p', rest)) : rest <:+ cs := by
  have hi : ∀ (str : String) (p2 : Nat) (r2 : List Char),
      readIriRef pos cs = .ok (str, p2, r2) → r2 <:+ cs :=
    fun str p2 r2 he => readIriRef_suffix _ _ _ _ _ he
  simp only [readPredicate] at h
  split at h <;> (try split at h) <;> (grind; done)

theorem readObject11_suffix (pos : Nat) (cs : List Char) (obj : Term) (p' : Nat)
    (rest : List Char) (h : readObject11 pos cs = .ok (obj, p', rest)) : rest <:+ cs := by
  have hi : ∀ (str : String) (p2 : Nat) (r2 : List Char),
      readIriRef pos cs = .ok (str, p2, r2) → r2 <:+ cs :=
    fun str p2 r2 he => readIriRef_suffix _ _ _ _ _ he
  have hb : ∀ (lab : String) (p2 : Nat) (r2 : List Char),
      readBlankNodeLabel pos cs = .ok (lab, p2, r2) → r2 <:+ cs :=
    fun lab p2 r2 he => readBlankNodeLabel_suffix _ _ _ _ _ he
  have hl : ∀ (li : WfLiteral) (p2 : Nat) (r2 : List Char),
      readLiteral .rdf11 pos cs = .ok (li, p2, r2) → r2 <:+ cs :=
    fun li p2 r2 he => readLiteral11_suffix _ _ _ _ _ he
  simp only [readObject11] at h
  split at h <;> (try split at h) <;> (try split at h) <;> (grind; done)

theorem readGraphLabel_suffix (pos : Nat) (cs : List Char) (g : Subject) (p' : Nat)
    (rest : List Char) (h : readGraphLabel pos cs = .ok (g, p', rest)) : rest <:+ cs := by
  have hi : ∀ (str : String) (p2 : Nat) (r2 : List Char),
      readIriRef pos cs = .ok (str, p2, r2) → r2 <:+ cs :=
    fun str p2 r2 he => readIriRef_suffix _ _ _ _ _ he
  have hb : ∀ (lab : String) (p2 : Nat) (r2 : List Char),
      readBlankNodeLabel pos cs = .ok (lab, p2, r2) → r2 <:+ cs :=
    fun lab p2 r2 he => readBlankNodeLabel_suffix _ _ _ _ _ he
  simp only [readGraphLabel] at h
  split at h <;> (try split at h) <;> (try split at h) <;> (grind; done)

theorem readOptGraphLabel_suffix (pos : Nat) (cs : List Char) (gopt : Option Subject)
    (p' : Nat) (rest : List Char)
    (h : readOptGraphLabel pos cs = .ok (gopt, p', rest)) : rest <:+ cs := by
  have hw := skipWs_suffix pos cs
  have hg : ∀ (g : Subject) (p2 : Nat) (r2 : List Char),
      readGraphLabel (skipWs pos cs).1 (skipWs pos cs).2 = .ok (g, p2, r2) → r2 <:+ cs :=
    fun g p2 r2 he => (readGraphLabel_suffix _ _ _ _ _ he).trans hw
  simp only [readOptGraphLabel] at h
  split at h <;> (try split at h) <;> (grind; done)

/-! ## A whole statement, and where its terminator is

The dot is not merely consumed — it is FOUND again inside the input,
which is what lets a caller conclude that a remainder cannot be empty
when the input ends with something else. -/

theorem readNQuad11_dot (pos : Nat) (cs : List Char) (tr : Triple)
    (g : Option Subject) (p' : Nat) (rest : List Char)
    (h : readNQuad11 pos cs = .ok (tr, g, p', rest)) : ('.' :: rest) <:+ cs := by
  simp only [readNQuad11] at h
  cases hw1 : skipWs pos cs with
  | mk pos1 cs1 =>
    have s1 : cs1 <:+ cs := by have := skipWs_suffix pos cs; rw [hw1] at this; exact this
    rw [hw1] at h; simp only at h
    cases hs : readSubject pos1 cs1 with
    | error e => rw [hs] at h; simp at h
    | ok v1 =>
      obtain ⟨subj, pos2, cs2⟩ := v1
      have s2 : cs2 <:+ cs1 := readSubject_suffix pos1 cs1 subj pos2 cs2 hs
      rw [hs] at h; simp only at h
      cases hw2 : skipWs pos2 cs2 with
      | mk pos3 cs3 =>
        have s3 : cs3 <:+ cs2 := by
          have := skipWs_suffix pos2 cs2; rw [hw2] at this; exact this
        rw [hw2] at h; simp only at h
        cases hp : readPredicate pos3 cs3 with
        | error e => rw [hp] at h; simp at h
        | ok v2 =>
          obtain ⟨pred, pos4, cs4⟩ := v2
          have s4 : cs4 <:+ cs3 := readPredicate_suffix pos3 cs3 pred pos4 cs4 hp
          rw [hp] at h; simp only at h
          cases hw3 : skipWs pos4 cs4 with
          | mk pos5 cs5 =>
            have s5 : cs5 <:+ cs4 := by
              have := skipWs_suffix pos4 cs4; rw [hw3] at this; exact this
            rw [hw3] at h; simp only at h
            cases ho : readObject11 pos5 cs5 with
            | error e => rw [ho] at h; simp at h
            | ok v3 =>
              obtain ⟨obj, pos6, cs6⟩ := v3
              have s6 : cs6 <:+ cs5 := readObject11_suffix pos5 cs5 obj pos6 cs6 ho
              rw [ho] at h; simp only at h
              cases hgl : readOptGraphLabel pos6 cs6 with
              | error e => rw [hgl] at h; simp at h
              | ok v4 =>
                obtain ⟨gopt, pos7, cs7⟩ := v4
                have s7 : cs7 <:+ cs6 :=
                  readOptGraphLabel_suffix pos6 cs6 gopt pos7 cs7 hgl
                rw [hgl] at h; simp only at h
                cases hw4 : skipWs pos7 cs7 with
                | mk pos8 cs8 =>
                  have s8 : cs8 <:+ cs7 := by
                    have := skipWs_suffix pos7 cs7; rw [hw4] at this; exact this
                  rw [hw4] at h; simp only at h
                  cases hc8 : cs8 with
                  | nil => rw [hc8] at h; simp at h
                  | cons d cs9 =>
                    rw [hc8] at h
                    by_cases hd : d = '.'
                    · subst hd
                      simp only [Except.ok.injEq, Prod.mk.injEq] at h
                      have hrest : cs9 = rest := by grind
                      subst hrest
                      rw [hc8] at s8
                      exact ((((((s8.trans s7).trans s6).trans s5).trans s4).trans
                        s3).trans s2).trans s1
                    · simp [hd] at h

#print axioms readSubject_suffix
#print axioms readPredicate_suffix
#print axioms readObject11_suffix
#print axioms readGraphLabel_suffix
#print axioms readOptGraphLabel_suffix
#print axioms readNQuad11_dot

#print axioms readLangTag_suffix
#print axioms readDatatype_suffix
#print axioms readLiteral11_suffix

#print axioms iriNextStep_emit_drop
#print axioms readIriRefBody_suffix
#print axioms readIriRef_suffix
#print axioms readBlankNodeLabel_suffix
#print axioms readStringLiteralQuoted_suffix

#print axioms span_snd_suffix
#print axioms skipWs_suffix
#print axioms skipToEol_suffix
#print axioms skipComment_suffix
#print axioms skipEol_suffix

end L4Factoidal.Syntax
