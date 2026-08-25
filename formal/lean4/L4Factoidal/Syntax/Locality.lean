/-
L4Factoidal.Syntax.Locality — the Lean counterpart of
`Parser.NTriples.Locality`.

## What locality is, and why both trees need it

A reader is LOCAL when appending more input after it has already stopped
does not change its answer. `RDF.NQuads.Streaming`'s
`theorem_stream_eq_batch` rests on it: a chunk boundary splits the input
into `complete ++ carry`, and streaming agrees with batching only if
parsing the complete part answers the same on `complete` as it does on
`complete ++ carry`.

The F\* module's own banner says two theorems are blocked on this same
wall, and diagnoses the cause: `"" ^ s == s` and `(a^b)^c == a^(b^c)`
both FAIL for symbolic strings, because Z3 has no associativity theory
for `FStar.String.strcat`. Its 2,848 lines re-state every scanner over
BYTE READS to get out from under that.

⚠️ **The Lean tree does NOT escape this.** `tools/lean-port-gap.py`
classified `Parser.NTriples.Locality` as needing no counterpart BY
DESIGN, and recorded no reason — the only entry in that table without
one. The reason it would have needed is false. A list-based reader can
still read past the end of a prefix: `List.span isBnodeChar` on
`"_:abc"` stops at the end of input, and on `"_:abc" ++ "d"` it consumes
the `d` as well. Locality has to be proved here too.

What IS different is the register. In Lean the statement is about list
suffixes, so the proof is structural induction rather than byte-index
arithmetic, and the side condition is visible in the statement: a reader
that stopped with input LEFT OVER is local; one that ran to the end of
its input is not, and cannot be.

## What is proved here

The pilot the F\* program itself chose — the IRI scanner — in the Lean
register:

* `iriEmitAt_local` — the escape-emitting step passes its remainder
  through untouched.
* `iriEmitAt_ne_close` — that step never closes an IRIREF, so the
  close-locality case analysis can discard it.
* `iriNextStep_close_local` — a step that CLOSED on `cs` closes at the
  same place on `cs ++ extra`.

## What is NOT proved here, named

`iriNextStep_emit_local` — the same statement for the EMIT outcome —
and everything above it: `readIriRefBody`, `readIriRef`,
`readBlankNodeLabel`, `readLiteral`, and the `readNQuad11` composition.
Without those the streaming-equals-batch theorem cannot be stated in
this tree either.

The emit case is not blocked on an idea; it is the same case analysis as
the close case with the two escape arms surviving instead of being
discarded, and those arms need `iriEmitAt_local` applied under the
equation compiler's `split`. It is left unproved rather than half-proved
because a named gap is checkable and a weakened theorem is not.

Tracked at <https://github.com/danbri/factoidal/issues/570>.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.Syntax.Lexing

namespace L4Factoidal.Syntax

/-! ## 1. Locality, and the side condition that does NOT work

⚠️ **A first version of this module defined locality with the condition
"the reader stopped with a non-empty remainder", and that definition is
FALSE.** It is recorded here rather than quietly replaced, because the
counterexample is the content.

`readBlankNodeLabel` pushes a trailing `.` BACK into its remainder,
since §19.8 forbids a label ending in a dot. So on `_:ab.` it answers
`("ab", 4, ['.'])` — remainder non-empty — while its span still ran to
the end of the input. Appending one character gives `("ab.c", 6, [])`, a
different label. `blankNode_stopped_short_is_not_enough` below exhibits
the pair.

The lesson generalises: no condition on a reader's OUTPUT can express
"it stopped because of something it saw", because a reader may hand back
characters it chose not to keep. The condition belongs on the INPUT, and
it is per-reader. `readIriRefBody` needs NO condition at all — a
successful IRI parse means the closing `>` was seen — while
`readBlankNodeLabel` needs its span to have stopped inside its own
input.

## What locality is

A reader is local when appending more input after it has already stopped
does not change its answer. `RDF.NQuads.Streaming`'s
`theorem_stream_eq_batch` rests on it: a chunk boundary splits the input
into `complete ++ carry`, and streaming agrees with batching only if
parsing the complete part answers the same either way. -/

/-- The blank-node reader's real precondition: its span stopped at a
character inside its own input, rather than running out. -/
def BnodeStopsInside (cs : List Char) : Prop :=
  ∀ (c2 : Char) (t : List Char), cs = '_' :: ':' :: c2 :: t →
    (t.span isBnodeChar).2 ≠ []

/-! ## 2. The escape-emitting step -/

/-- The step that emits a decoded escape never closes an IRIREF. This
is what lets the close-locality analysis discard both escape arms. -/
theorem iriEmitAt_ne_close (cp pos width : Nat) (rest : List Char)
    (which : String) (r : List Char) :
    iriEmitAt cp pos width rest which ≠ .close r := by
  unfold iriEmitAt
  split
  · simp
  · split <;> simp

/-- The escape step passes its remainder through untouched, so
appending to the input appends to the remainder. -/
theorem iriEmitAt_local (cp pos width : Nat) (rest extra : List Char)
    (which : String) (c : Char) (w : Nat) (r : List Char)
    (h : iriEmitAt cp pos width rest which = .emit c w r) :
    iriEmitAt cp pos width (rest ++ extra) which = .emit c w (r ++ extra) := by
  unfold iriEmitAt at h ⊢
  split at h
  · simp at h
  · split at h
    · simp at h
    · simp_all

/-! ## 3. Closing is local -/

set_option maxHeartbeats 4000000 in
/-- **A step that closed the IRIREF closes at the same place on longer
input.** The `>` is already in `cs`, so nothing appended after it can
move the close. -/
theorem iriNextStep_close_local (pos : Nat) (cs extra rest : List Char)
    (h : iriNextStep pos cs = .close rest) :
    iriNextStep pos (cs ++ extra) = .close (rest ++ extra) := by
  unfold iriNextStep at h ⊢
  split at h <;> (try split at h) <;> simp_all [iriEmitAt_ne_close]

/-! ## 3b. Emitting is local too

The same case analysis as the close case, with the two escape arms
SURVIVING instead of being discarded — each discharged by
`iriEmitAt_local` — and the plain-character arm needing `c` shown to be
neither `>` nor `\`, which the equation compiler leaves as two
negative hypotheses about the tail rather than one about the head. -/

set_option maxHeartbeats 4000000 in
theorem iriNextStep_emit_local (pos : Nat) (cs extra rest : List Char)
    (c : Char) (w : Nat) (h : iriNextStep pos cs = .emit c w rest) :
    iriNextStep pos (cs ++ extra) = .emit c w (rest ++ extra) := by
  unfold iriNextStep at h ⊢
  split at h
  all_goals (try split at h)
  all_goals (try simp_all)
  all_goals (first
    | exact iriEmitAt_local _ _ _ _ _ _ _ _ _ h
    | (rename_i hh; exact iriEmitAt_local _ _ _ _ _ _ _ _ _ hh)
    | (rename_i _hgt hb1 hb2 hfb
       have hcb : ¬ c = '\\' := by
         intro hb
         cases hr : rest with
         | nil => exact absurd (hr ▸ rfl) (hb1 hb)
         | cons a t => exact absurd (hr ▸ rfl) (hb2 a t hb)
       obtain ⟨h1, h2, h3⟩ := h
       subst h1; subst h2; subst h3
       simp [hcb, Nat.not_le.mpr hfb.1, hfb.2]))

/-! ## 5. The IRI body recursion

`readIriRefBody`'s `match h : iriNextStep pos cs with` binds the step's
own equation, because the termination argument needs it. That makes the
match DEPENDENT, so rewriting its scrutinee breaks the motive. The three
equations below re-state each arm without the binder, which is what lets
the locality induction rewrite at all — the same move the F\* tree makes
for a different reason. -/


theorem readIriRefBody_close_eq (pos : Nat) (cs rest : List Char)
    (h : iriNextStep pos cs = .close rest) :
    readIriRefBody pos cs = .ok ("", pos + 1, rest) := by
  rw [readIriRefBody]; split <;> simp_all

theorem readIriRefBody_fail_eq (pos : Nat) (cs : List Char) (e : ParseError)
    (h : iriNextStep pos cs = .fail e) :
    readIriRefBody pos cs = .error e := by
  rw [readIriRefBody]; split <;> simp_all

theorem readIriRefBody_emit_eq (pos : Nat) (cs r : List Char) (c : Char) (w : Nat)
    (h : iriNextStep pos cs = .emit c w r) :
    readIriRefBody pos cs
      = (readIriRefBody (pos + w) r).map (fun (s, p, rr) => (c.toString ++ s, p, rr)) := by
  rw [readIriRefBody]; split <;> simp_all



theorem readIriRefBody_local : ∀ (n : Nat) (cs : List Char), cs.length ≤ n →
    ∀ (pos : Nat) (extra : List Char) (s : String) (p' : Nat) (rest : List Char),
    readIriRefBody pos cs = .ok (s, p', rest) →
    readIriRefBody pos (cs ++ extra) = .ok (s, p', rest ++ extra)
  | 0, cs, hn, pos, extra, s, p', rest, h => by
      have hcs : cs = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hcs
      rw [readIriRefBody_fail_eq pos [] _ rfl] at h
      simp at h
  | n + 1, cs, hn, pos, extra, s, p', rest, h => by
      cases hstep : iriNextStep pos cs with
      | fail e => rw [readIriRefBody_fail_eq pos cs e hstep] at h; simp at h
      | close r =>
          rw [readIriRefBody_close_eq pos cs r hstep] at h
          simp at h
          obtain ⟨h1, h2, h3⟩ := h
          subst h1; subst h2; subst h3
          rw [readIriRefBody_close_eq pos (cs ++ extra) (r ++ extra)
                (iriNextStep_close_local pos cs extra r hstep)]
      | emit c w r =>
          have hshort : r.length < cs.length := iriNextStep_emit_shorter hstep
          rw [readIriRefBody_emit_eq pos cs r c w hstep] at h
          cases hrec : readIriRefBody (pos + w) r with
          | error e => rw [hrec] at h; simp [Except.map] at h
          | ok v =>
              obtain ⟨s2, p2, r2⟩ := v
              rw [readIriRefBody_emit_eq pos (cs ++ extra) (r ++ extra) c w
                    (iriNextStep_emit_local pos cs extra r c w hstep),
                  readIriRefBody_local n r (by omega) (pos + w) extra s2 p2 r2 hrec]
              rw [hrec] at h
              simp [Except.map] at h ⊢
              obtain ⟨h1, h2, h3⟩ := h
              subst h1; subst h2; subst h3
              simp

/-- **The IRIREF reader is local.** A closed IRIREF stays closed and
keeps its text when more input follows. -/
theorem readIriRef_local (pos : Nat) (cs extra : List Char) (s : String)
    (p' : Nat) (rest : List Char) (h : readIriRef pos cs = .ok (s, p', rest)) :
    readIriRef pos (cs ++ extra) = .ok (s, p', rest ++ extra) := by
  cases cs with
  | nil => simp [readIriRef] at h
  | cons c0 r0 =>
      by_cases hlt : c0 = '<'
      · subst hlt
        simp only [readIriRef, List.cons_append] at h ⊢
        exact readIriRefBody_local (r0.length) r0 (by omega) (pos + 1) extra s p'
          rest h
      · simp only [readIriRef] at h
        cases c0 <;> simp_all

/-! ## 4b. Why the side condition cannot be dropped

⚠️ **Locality is FALSE without the stopped-short condition.** The
blank-node reader spans as far as the input allows, so `_:abc` scans a
three-character label on its own and a four-character one when a `d`
follows. Any statement that drops `rest ≠ []` is refuted by that pair.

It is recorded below as two `#guard`s rather than as a theorem because
the values differ only in a `String`, and the kernel does not reduce
`String` equality — the same reason several other modules in this port
pin string-valued facts with `#guard`. -/

/-! ## 6. Spans, and the blank-node reader

`List.span` is where the trailing-dot counterexample lives, so its
locality lemma carries the stopped-inside condition explicitly. -/


theorem spanLoop_append_of_stopped {α : Type} (p : α → Bool) :
    ∀ (cs acc taken : List α) (a : α) (dropped extra : List α),
      List.span.loop p cs acc = (taken, a :: dropped) →
      List.span.loop p (cs ++ extra) acc = (taken, a :: (dropped ++ extra))
  | [], acc, taken, a, dropped, extra, h => by
      simp [List.span.loop] at h
  | c :: t, acc, taken, a, dropped, extra, h => by
      simp only [List.span.loop, List.cons_append] at h ⊢
      by_cases hp : p c
      · simp only [hp, if_pos] at h ⊢
        exact spanLoop_append_of_stopped p t (c :: acc) taken a dropped extra h
      · simp only [hp, if_neg, Bool.false_eq_true, not_false_eq_true] at h ⊢
        simp at h
        obtain ⟨h1, h2, h3⟩ := h
        subst h1; subst h2; subst h3
        simp

theorem span_append_of_stopped {α : Type} (p : α → Bool)
    (cs taken : List α) (a : α) (dropped extra : List α)
    (h : cs.span p = (taken, a :: dropped)) :
    (cs ++ extra).span p = (taken, a :: (dropped ++ extra)) := by
  simp only [List.span] at h ⊢
  exact spanLoop_append_of_stopped p cs [] taken a dropped extra h


/-- **The blank-node reader is local when it stopped short.** Its span
runs to the end of the input, so the non-empty remainder is doing real
work here — `readBlankNodeLabel_not_local_at_end`'s guard pair is the
refutation of the version without it. -/
theorem readBlankNodeLabel_local (pos : Nat) (cs extra : List Char) (s : String)
    (p' : Nat) (rest : List Char)
    (h : readBlankNodeLabel pos cs = .ok (s, p', rest))
    (hstop : BnodeStopsInside cs) :
    readBlankNodeLabel pos (cs ++ extra) = .ok (s, p', rest ++ extra) := by
  cases cs with
  | nil => simp [readBlankNodeLabel] at h
  | cons c0 r0 =>
    by_cases h0 : c0 = '_'
    · subst h0
      cases r0 with
      | nil => simp [readBlankNodeLabel] at h
      | cons c1 r1 =>
        by_cases h1 : c1 = ':'
        · subst h1
          cases r1 with
          | nil => simp [readBlankNodeLabel] at h
          | cons c2 t =>
            simp only [readBlankNodeLabel, List.cons_append] at h ⊢
            by_cases hst : isBnodeStartChar c2
            · simp only [hst, Bool.not_eq_true', Bool.true_eq_false,
                         if_neg, not_false_eq_true] at h ⊢
              cases hsp : t.span isBnodeChar with
              | mk taken droppedList =>
                  rw [hsp] at h
                  cases hdl : droppedList with
                  | nil =>
                      -- excluded by the precondition: the span ran out
                      have hsp2 : (t.span isBnodeChar).2 = [] := by
                        rw [hsp, hdl]
                      exact absurd hsp2 (hstop c2 t rfl)
                  | cons a dr =>
                      rw [hdl] at h
                      have hsp2 : t.span isBnodeChar = (taken, a :: dr) := by
                        rw [hsp, hdl]
                      rw [span_append_of_stopped isBnodeChar t taken a dr extra hsp2]
                      split at h <;> (try split) <;> simp_all
                      all_goals
                        (obtain ⟨_, _, e3⟩ := h
                         subst e3
                         simp)
            · simp only [hst, Bool.not_eq_true', if_pos] at h
              simp at h
        · simp [readBlankNodeLabel, h1] at h
    · simp [readBlankNodeLabel, h0] at h


/-! ## Build-time checks -/

/-! Closing is local on a worked case. -/
#guard (match iriNextStep 0 "a>".toList with
         | .emit c _ r => c == 'a' && r == ">".toList | _ => false)
#guard (match iriNextStep 0 ">rest".toList with
         | .close r => r == "rest".toList | _ => false)
#guard (match iriNextStep 0 (">".toList ++ "more".toList) with
         | .close r => r == "more".toList | _ => false)

/-! ⚠️ And the step is NOT local when the input runs out mid-escape: on
its own the truncated escape fails, with more input it emits. This is
the reason `iriNextStep_emit_local` needs the same care as the close
case rather than being a corollary of it. -/
#guard (match iriNextStep 0 "\\u00".toList with
         | .fail _ => true | _ => false) == true
#guard (match iriNextStep 0 ("\\u00".toList ++ "41".toList) with
         | .fail _ => true | _ => false) == false

/-! The blank-node reader spans to the end of input. -/
#guard (readBlankNodeLabel 0 "_:abc".toList).toOption.map (fun x => x.1)
        == some "abc"
#guard (readBlankNodeLabel 0 "_:abcd".toList).toOption.map (fun x => x.1)
        == some "abcd"

/-! ⚠️ **And the trailing-dot case refutes the output-only condition.**
`_:ab.` stops with a NON-EMPTY remainder — the pushed-back dot — and is
still not local: one more character changes the label. This is the pair
that killed the first version of this module's `ReaderLocal`. -/
#guard (readBlankNodeLabel 0 "_:ab.".toList).toOption.map (fun x => x.2.2)
        == some ['.']
#guard (readBlankNodeLabel 0 "_:ab.".toList).toOption.map (fun x => x.1)
        == some "ab"
#guard (readBlankNodeLabel 0 ("_:ab.".toList ++ "c".toList)).toOption.map
        (fun x => x.1) == some "ab.c"

/-! And the precondition that DOES work excludes exactly that case. -/
#guard (("bc".toList).span isBnodeChar).2 == ([] : List Char)
#guard (("bc>".toList).span isBnodeChar).2 == ['>']

/-! ## Axiom audit -/

#print axioms iriEmitAt_local
#print axioms iriEmitAt_ne_close
#print axioms iriNextStep_close_local
#print axioms iriNextStep_emit_local
#print axioms readIriRefBody_local
#print axioms readIriRef_local
#print axioms span_append_of_stopped
#print axioms readBlankNodeLabel_local

end L4Factoidal.Syntax
