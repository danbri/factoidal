/-
L4Factoidal.Syntax.NQuadsHomomorphism — streaming agrees with batch.

`streamParse11_eq_batch`: whatever dataset the chunk fold produces,
parsing the whole document at once produces the same one. This is the
theorem `Syntax/NQuadsStreaming.lean` was built toward, and the Lean
counterpart of the F\* module's `theorem_stream_eq_batch`.

The invariant carried through the fold (`foldl_feedChunk_inv`): the
text consumed so far ends at a line boundary, the stored offset equals
its length, and parsing it from position zero yields the stored
dataset. Each `feedChunk` step extends it by `parseQuadLines11_concat`
(`Syntax/NQuadsConcat.lean`); `finish` closes it the same way.

Stated for a fold that ENDS WITHOUT ERROR. A failed stream is sticky
(`feedChunk_error_sticky`) and reports the error instead of a dataset;
equating error CASES additionally needs the converse concatenation
direction recorded in `NQuadsConcat.lean`'s header.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.Syntax.NQuadsConcat

namespace L4Factoidal.Syntax.NQuadsStreaming
open L4Factoidal.RDF
open L4Factoidal.Syntax

theorem foldl_err_sticky : ∀ (chunks : List (List Char)) (st : StreamState)
    (e : ParseError), st.err = some e →
    (chunks.foldl (feedChunk .rdf11) st).err = some e
  | [], st, e, h => h
  | c :: rest, st, e, h => by
      simp only [List.foldl_cons]
      rw [feedChunk_error_sticky .rdf11 st c e h]
      exact foldl_err_sticky rest st e h

theorem endsWithNewline_append (a b : List Char)
    (ha : EndsWithNewline a) (hb : EndsWithNewline b) : EndsWithNewline (a ++ b) := by
  rcases hb with hb | hb
  · subst hb; simpa using ha
  · right
    have hbne : b ≠ [] := by intro hc; rw [hc] at hb; simp at hb
    rw [getLast?_append_ne a b hbne]; exact hb

/-- **Streaming agrees with batch.** Whatever dataset the chunk fold
produces, parsing the whole document at once produces the same one. -/
theorem foldl_feedChunk_inv : ∀ (chunks : List (List Char)) (st : StreamState)
    (consumed : List Char),
      st.err = none → st.pos = consumed.length → EndsWithNewline consumed →
      parseFrom .rdf11 0 consumed Dataset.empty = .ok st.ds →
      (chunks.foldl (feedChunk .rdf11) st).err = none →
      ∃ consumed',
        consumed' ++ (chunks.foldl (feedChunk .rdf11) st).carry
          = consumed ++ st.carry ++ chunks.flatten ∧
        (chunks.foldl (feedChunk .rdf11) st).pos = consumed'.length ∧
        EndsWithNewline consumed' ∧
        parseFrom .rdf11 0 consumed' Dataset.empty
          = .ok (chunks.foldl (feedChunk .rdf11) st).ds
  | [], st, consumed, herr, hpos, hend, hds, _ => by
      exact ⟨consumed, by simp, hpos, hend, hds⟩
  | c :: rest, st, consumed, herr, hpos, hend, hds, hfinal => by
      simp only [List.foldl_cons] at hfinal ⊢
      cases hp : parseFrom .rdf11 st.pos (splitCompleteLines (st.carry ++ c)).1 st.ds with
      | error e =>
          exfalso
          have hse : (feedChunk .rdf11 st c).err = some e := by
            simp only [feedChunk, herr, hp]
          rw [foldl_err_sticky rest _ e hse] at hfinal
          simp at hfinal
      | ok ds' =>
          have hst' : feedChunk .rdf11 st c
              = { ds := ds', carry := (splitCompleteLines (st.carry ++ c)).2,
                  pos := st.pos + (splitCompleteLines (st.carry ++ c)).1.length,
                  err := none } := by
            simp only [feedChunk, herr, hp]
          have hrec : (splitCompleteLines (st.carry ++ c)).1
              ++ (splitCompleteLines (st.carry ++ c)).2 = st.carry ++ c :=
            splitCompleteLines_reconstruct (st.carry ++ c)
          have hcompEnd : EndsWithNewline (splitCompleteLines (st.carry ++ c)).1 := by
            rcases splitCompleteLines_complete_ends_newline (st.carry ++ c) with hx | hx
            · exact Or.inl hx
            · right
              cases hg : (splitCompleteLines (st.carry ++ c)).1.getLast? with
              | none => rw [hg] at hx; simp at hx
              | some x => rw [hg] at hx; simp [isNl] at hx; rw [hx]
          have hnew : parseFrom .rdf11 0
              (consumed ++ (splitCompleteLines (st.carry ++ c)).1) Dataset.empty = .ok ds' := by
            simp only [parseFrom] at hds hp ⊢
            rw [parseQuadLines11_concat consumed.length consumed (by omega)
                  (splitCompleteLines (st.carry ++ c)).1 0
                  ((consumed ++ (splitCompleteLines (st.carry ++ c)).1).length + 1)
                  Dataset.empty st.ds hend (by simp) hds]
            rw [Nat.zero_add, ← hpos]
            exact hp
          have := foldl_feedChunk_inv rest (feedChunk .rdf11 st c)
            (consumed ++ (splitCompleteLines (st.carry ++ c)).1)
            (by rw [hst']) (by rw [hst']; simp; omega)
            (endsWithNewline_append _ _ hend hcompEnd) (by rw [hst']; exact hnew) hfinal
          obtain ⟨cc, h1, h2, h3, h4⟩ := this
          refine ⟨cc, ?_, h2, h3, h4⟩
          rw [h1, hst']
          simp only [List.append_assoc, hrec]
          simp

theorem streamParse11_eq_batch (chunks : List (List Char)) (r : Dataset)
    (h : streamParse .rdf11 chunks = .ok r) :
    parseFrom .rdf11 0 chunks.flatten Dataset.empty = .ok r := by
  simp only [streamParse, finish] at h
  cases hE : (chunks.foldl (feedChunk .rdf11) initialState).err with
  | some e => rw [hE] at h; simp at h
  | none =>
      rw [hE] at h
      simp only at h
      obtain ⟨cc, h1, h2, h3, h4⟩ :=
        foldl_feedChunk_inv chunks initialState [] rfl rfl (Or.inl rfl)
          (by simp [parseFrom, initialState, parseQuadLinesAcc, skipWs, List.span,
                    List.span.loop]) hE
      have h1' : cc ++ (chunks.foldl (feedChunk .rdf11) initialState).carry
          = chunks.flatten := by rw [h1]; simp [initialState]
      simp only [parseFrom] at h h4 ⊢
      rw [← h1']
      rw [parseQuadLines11_concat cc.length cc (by omega)
            (chunks.foldl (feedChunk .rdf11) initialState).carry 0
            ((cc ++ (chunks.foldl (feedChunk .rdf11) initialState).carry).length + 1)
            Dataset.empty (chunks.foldl (feedChunk .rdf11) initialState).ds h3 (by simp) h4]
      rw [Nat.zero_add, ← h2]
      exact h

/-! ## Axiom audit -/

#print axioms foldl_feedChunk_inv
#print axioms streamParse11_eq_batch

end L4Factoidal.Syntax.NQuadsStreaming
