/-
L4Factoidal.Syntax.LocalitySkips — locality for the three skips, and the
list facts they rest on.

A chunk handed to the streaming parser ends with a newline. These
lemmas are what turn that into the side conditions the readers need:

* `span_snd_ne_nil_of_last` — a span stops when the last character
  fails its test, so whitespace never runs off the end of a chunk;
* `getLast?_of_suffix` — a non-empty suffix keeps the last character,
  so "still ends with a newline" survives every reader;
* `skipToEol_local`, `skipComment_local`, `skipEol_local`.

⚠️ Each locality lemma carries a side condition, and each is real. A
`skipToEol` that ran off the end keeps running. A `skipComment` on an
empty input can be turned into a comment by appending a `#`. A
`skipEol` on exactly `['\r']` becomes a CRLF pair when a `\n` arrives.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.Syntax.LocalitySuffix

namespace L4Factoidal.Syntax
open L4Factoidal.RDF

/-! ## Everything a span consumed satisfied the test -/

theorem spanLoop_fst_all {α : Type} (p : α → Bool) :
    ∀ (l acc : List α) (c : α), c ∈ (List.span.loop p l acc).1 →
      c ∈ acc ∨ p c = true
  | [], acc, c, h => by
      simp [List.span.loop] at h
      exact Or.inl h
  | x :: t, acc, c, h => by
      simp only [List.span.loop] at h
      by_cases hp : p x
      · simp only [hp, if_pos] at h
        rcases spanLoop_fst_all p t (x :: acc) c h with hc | hc
        · simp at hc
          rcases hc with hc | hc
          · exact Or.inr (by rw [hc]; exact hp)
          · exact Or.inl hc
        · exact Or.inr hc
      · simp only [hp, Bool.false_eq_true, if_neg, not_false_eq_true] at h
        simp at h
        exact Or.inl h

theorem span_fst_all {α : Type} (p : α → Bool) (l : List α) (c : α)
    (h : c ∈ (l.span p).1) : p c = true := by
  rcases spanLoop_fst_all p l [] c h with hc | hc
  · simp at hc
  · exact hc

/-! ## A span stops when the last character fails the test -/

theorem mem_of_getLast? {α : Type} {l : List α} {a : α} (h : l.getLast? = some a) :
    a ∈ l := by
  have := list_getLast?_split l a h
  rw [this]
  simp

theorem span_snd_ne_nil_of_last {α : Type} (p : α → Bool) (l : List α) (a : α)
    (h : l.getLast? = some a) (hp : p a = false) : (l.span p).2 ≠ [] := by
  intro hc
  have hall : (l.span p).1 = l := by
    have := span_append p l
    rw [hc] at this; simpa using this
  have hmem : a ∈ (l.span p).1 := by rw [hall]; exact mem_of_getLast? h
  have := span_fst_all p l a hmem
  rw [hp] at this
  simp at this

/-! ## A non-empty suffix keeps the last character -/

theorem getLast?_append_ne {α : Type} : ∀ (pre r : List α), r ≠ [] →
    (pre ++ r).getLast? = r.getLast?
  | [], r, _ => by simp
  | x :: t, r, hr => by
      have ih := getLast?_append_ne t r hr
      have hne : t ++ r ≠ [] := by
        intro hc; simp at hc; exact hr hc.2
      cases hc : t ++ r with
      | nil => exact absurd hc hne
      | cons y ys =>
          simp only [List.cons_append, hc, List.getLast?_cons_cons]
          rw [← hc]; exact ih

theorem getLast?_of_suffix {α : Type} {r l : List α} {a : α}
    (hs : r <:+ l) (hne : r ≠ []) (h : l.getLast? = some a) : r.getLast? = some a := by
  obtain ⟨pre, hpre⟩ := hs
  rw [← hpre] at h
  rwa [getLast?_append_ne pre r hne] at h


/-! ## Locality of the skips

⚠️ Each carries a side condition, and each is real. A `skipToEol` that
ran off the end keeps running; a `skipComment` on an empty input can be
turned into a comment by appending a `#`; a `skipEol` on exactly `['\r']`
becomes a CRLF pair when a `\n` is appended. -/

theorem skipToEol_local : ∀ (pos : Nat) (cs extra : List Char),
    (skipToEol pos cs).2 ≠ [] →
    skipToEol pos (cs ++ extra) = ((skipToEol pos cs).1, (skipToEol pos cs).2 ++ extra)
  | pos, [], extra, h => by simp [skipToEol] at h
  | pos, c :: t, extra, h => by
      simp only [List.cons_append]
      by_cases hn : c = '\n'
      · subst hn; simp [skipToEol]
      · by_cases hr : c = '\r'
        · subst hr; simp [skipToEol]
        · have h1 : skipToEol pos (c :: t) = skipToEol (pos + 1) t := by
            simp [skipToEol, hn, hr]
          have h2 : skipToEol pos (c :: (t ++ extra)) = skipToEol (pos + 1) (t ++ extra) := by
            simp [skipToEol, hn, hr]
          rw [h1] at h
          rw [h2, h1]
          exact skipToEol_local (pos + 1) t extra h

theorem skipComment_local (pos : Nat) (cs extra : List Char) (hne : cs ≠ [])
    (h : (skipComment pos cs).2 ≠ []) :
    skipComment pos (cs ++ extra)
      = ((skipComment pos cs).1, (skipComment pos cs).2 ++ extra) := by
  cases cs with
  | nil => exact absurd rfl hne
  | cons c t =>
    simp only [List.cons_append]
    by_cases hc : c = '#'
    · subst hc
      have h1 : skipComment pos ('#' :: t) = skipToEol (pos + 1) t := rfl
      have h2 : skipComment pos ('#' :: (t ++ extra)) = skipToEol (pos + 1) (t ++ extra) := rfl
      rw [h1] at h
      rw [h2, h1]
      exact skipToEol_local (pos + 1) t extra h
    · have h1 : skipComment pos (c :: t) = (pos, c :: t) := by simp [skipComment, hc]
      have h2 : skipComment pos (c :: (t ++ extra)) = (pos, c :: (t ++ extra)) := by
        simp [skipComment, hc]
      rw [h2, h1]
      simp

theorem skipEol_local (pos : Nat) (cs extra : List Char) (hne : cs ≠ [])
    (hcr : cs ≠ ['\r']) :
    skipEol pos (cs ++ extra) = ((skipEol pos cs).1, (skipEol pos cs).2 ++ extra) := by
  cases cs with
  | nil => exact absurd rfl hne
  | cons c t =>
    simp only [List.cons_append]
    by_cases hr : c = '\r'
    · subst hr
      cases t with
      | nil => exact absurd rfl hcr
      | cons b t2 =>
        simp only [List.cons_append]
        by_cases hb : b = '\n'
        · subst hb
          have h1 : skipEol pos ('\r' :: '\n' :: t2) = (pos + 2, t2) := rfl
          have h2 : skipEol pos ('\r' :: '\n' :: (t2 ++ extra)) = (pos + 2, t2 ++ extra) := rfl
          rw [h2, h1]
        · have h1 : skipEol pos ('\r' :: b :: t2) = (pos + 1, b :: t2) := by
            simp [skipEol, hb]
          have h2 : skipEol pos ('\r' :: b :: (t2 ++ extra))
              = (pos + 1, b :: (t2 ++ extra)) := by
            simp [skipEol, hb]
          rw [h2, h1]
          simp
    · by_cases hn : c = '\n'
      · subst hn
        have h1 : skipEol pos ('\n' :: t) = (pos + 1, t) := rfl
        have h2 : skipEol pos ('\n' :: (t ++ extra)) = (pos + 1, t ++ extra) := rfl
        rw [h2, h1]
      · have h1 : skipEol pos (c :: t) = (pos, c :: t) := by simp [skipEol, hr, hn]
        have h2 : skipEol pos (c :: (t ++ extra)) = (pos, c :: (t ++ extra)) := by
          simp [skipEol, hr, hn]
        rw [h2, h1]
        simp

#print axioms skipToEol_local
#print axioms skipComment_local
#print axioms skipEol_local

#print axioms span_fst_all
#print axioms span_snd_ne_nil_of_last
#print axioms getLast?_of_suffix

end L4Factoidal.Syntax
