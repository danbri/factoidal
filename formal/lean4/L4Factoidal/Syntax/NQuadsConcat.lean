/-
L4Factoidal.Syntax.NQuadsConcat — the line-boundary concatenation lemma.

`Syntax/NQuadsStreaming.lean`'s header names ONE thing as missing: that
parsing `a ++ b`, where `a` ends in a newline, equals parsing `b` from
the state parsing `a` reached. That is the F\* module's
`lemma_parse_nquads_acc_concat_line_general`, and the bulk of its 3,438
lines. `parseQuadLines11_concat` is it.

ⓘ It is stated in ok-form: it assumes the `complete` half parses. That
is the direction the streaming fold needs, since the fold has already
run that half and holds its dataset. ⚠️ The converse — if the combined
run succeeds then the `complete` half does — is NOT proved here, and it
is not free: it needs the fact that no reader consumes a raw newline,
which is true of this grammar (IRIs forbid raw control characters,
literals forbid a raw newline, inline whitespace is space and tab only)
but has no proof in the tree yet.

The proof is one round of the parser at a time, over four branches
(blank/comment line, LF, CR, statement). Each round needs four things,
and each comes from a module below this one:

* the round answers the same on the longer input — `skipWs_local`,
  `skipComment_local`, `skipEol_local`, `readNQuad11_local`;
* what is left still ends with a newline — `getLast?_of_suffix` over
  the suffix lemmas;
* the position advanced by exactly what was consumed —
  `Syntax.LocalityCount`, which is what makes the two runs line up;
* the remaining fuel is still enough —
  `parseQuadLinesAcc11_fuel_indep`.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.Syntax.NQuadsStreaming

namespace L4Factoidal.Syntax.NQuadsStreaming
open L4Factoidal.RDF
open L4Factoidal.Syntax

/-- A buffer the streaming splitter can hand to the parser: empty, or
ending at a line boundary. -/
def EndsWithNewline (cs : List Char) : Prop :=
  cs = [] ∨ cs.getLast? = some '\n'

/-! ## The skips stop when a newline is still ahead -/

theorem skipToEol_stops : ∀ (pos : Nat) (cs : List Char),
    cs.getLast? = some '\n' → (skipToEol pos cs).2 ≠ []
  | pos, [], h => by simp at h
  | pos, c :: t, h => by
      by_cases hn : c = '\n'
      · subst hn; simp [skipToEol]
      · by_cases hr : c = '\r'
        · subst hr; simp [skipToEol]
        · have ht : t ≠ [] := by
            intro hc; subst hc; simp at h; exact hn h
          have hlt : t.getLast? = some '\n' :=
            getLast?_of_suffix (List.suffix_cons c t) ht h
          have he : skipToEol pos (c :: t) = skipToEol (pos + 1) t := by
            simp [skipToEol, hn, hr]
          rw [he]
          exact skipToEol_stops (pos + 1) t hlt

theorem skipComment_stops (pos : Nat) (cs : List Char)
    (h : cs.getLast? = some '\n') : (skipComment pos cs).2 ≠ [] := by
  cases cs with
  | nil => simp at h
  | cons c t =>
    by_cases hc : c = '#'
    · subst hc
      have ht : t ≠ [] := by
        intro hcc; subst hcc; simp at h
      have hlt : t.getLast? = some '\n' :=
        getLast?_of_suffix (List.suffix_cons '#' t) ht h
      have he : skipComment pos ('#' :: t) = skipToEol (pos + 1) t := rfl
      rw [he]
      exact skipToEol_stops (pos + 1) t hlt
    · have he : skipComment pos (c :: t) = (pos, c :: t) := by simp [skipComment, hc]
      rw [he]; simp

theorem ne_singleton_cr_of_last {cs : List Char} (h : cs.getLast? = some '\n') :
    cs ≠ ['\r'] := by
  intro hc; rw [hc] at h; simp at h

/-! ## The empty-buffer case -/

private theorem concat_nil (carry : List Char) (pos f : Nat) (ds dsMid : Dataset)
    (hf : carry.length < f)
    (hmid : parseQuadLinesAcc .rdf11 1 pos [] ds = .ok dsMid) :
    parseQuadLinesAcc .rdf11 f pos carry ds
      = parseQuadLinesAcc .rdf11 (carry.length + 1) pos carry dsMid := by
  have hds : dsMid = ds := by
    simp [parseQuadLinesAcc, skipWs, List.span, List.span.loop] at hmid
    exact hmid.symm
  subst hds
  exact parseQuadLinesAcc11_fuel_indep f (carry.length + 1) pos carry dsMid
    (by omega) (by omega)


/-! ## The line-boundary concatenation lemma

Parsing `complete ++ carry`, where `complete` ends at a line boundary,
is parsing `complete` and then parsing `carry` from where that stopped.

ⓘ Stated in ok-form: it assumes the `complete` half parses. That is the
direction the streaming fold needs — the fold has already run the
`complete` half and holds its dataset. The converse (if the combined
run succeeds then the `complete` half does) needs a different fact,
that no reader consumes a raw newline, and is not proved here. -/

theorem parseQuadLines11_concat :
    ∀ (n : Nat) (complete : List Char), complete.length ≤ n →
    ∀ (carry : List Char) (pos f : Nat) (ds dsMid : Dataset),
      EndsWithNewline complete →
      (complete ++ carry).length < f →
      parseQuadLinesAcc .rdf11 (complete.length + 1) pos complete ds = .ok dsMid →
      parseQuadLinesAcc .rdf11 f pos (complete ++ carry) ds
        = parseQuadLinesAcc .rdf11 (carry.length + 1) (pos + complete.length) carry dsMid
  | 0, complete, hn, carry, pos, f, ds, dsMid, _, hf, hmid => by
      have hnil : complete = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hnil
      simp only [List.nil_append, List.length_nil, Nat.add_zero] at *
      exact concat_nil carry pos f ds dsMid (by omega) hmid
  | n + 1, complete, hn, carry, pos, f, ds, dsMid, hend, hf, hmid => by
    rcases hend with hnil | hlastC
    · subst hnil
      simp only [List.nil_append, List.length_nil, Nat.add_zero] at *
      exact concat_nil carry pos f ds dsMid (by omega) hmid
    · have hnfC : complete ≠ [] := by
        intro hc; rw [hc] at hlastC; simp at hlastC
      have hlenC : 1 ≤ complete.length := by
        cases complete with
        | nil => exact absurd rfl hnfC
        | cons _ _ => simp
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      have hne1 : (skipWs pos complete).2 ≠ [] := by
        have := span_snd_ne_nil_of_last isNtWs complete '\n' hlastC (by decide)
        simpa [skipWs] using this
      have hloc1 := skipWs_local pos complete carry hne1
      have hcnt1 := skipWs_counts pos complete
      have hlast1 : (skipWs pos complete).2.getLast? = some '\n' :=
        getLast?_of_suffix (skipWs_suffix pos complete) hne1 hlastC
      have hlen1 : (skipWs pos complete).2.length ≤ complete.length :=
        (skipWs_suffix pos complete).length_le
      cases hw : skipWs pos complete with
      | mk pos1 cs1 =>
        rw [hw] at hne1 hloc1 hcnt1 hlast1 hlen1
        simp only at hne1 hloc1 hcnt1 hlast1 hlen1
        generalize hRHS :
          parseQuadLinesAcc .rdf11 (carry.length + 1) (pos + complete.length) carry dsMid = RHS
        simp only [parseQuadLinesAcc] at hmid ⊢
        rw [hw] at hmid
        rw [hloc1]
        simp only at hmid ⊢
        cases hc1 : cs1 with
        | nil => exact absurd hc1 hne1
        | cons a t =>
          rw [hc1] at hmid hlast1 hlen1 hcnt1
          simp only [List.cons_append] at hmid ⊢
          simp only [List.length_cons] at hlen1 hcnt1
          simp only [List.length_append] at hf
          by_cases hh : a = '#'
          · subst hh
            have hstop := skipComment_stops pos1 ('#' :: t) hlast1
            cases hcm : skipComment pos1 ('#' :: t) with
            | mk p2 c2 =>
              rw [hcm] at hstop
              simp only at hstop
              have hc2last : c2.getLast? = some '\n' := by
                have hs := skipComment_suffix pos1 ('#' :: t)
                rw [hcm] at hs; simp only at hs
                exact getLast?_of_suffix hs hstop hlast1
              have hc2len : c2.length ≤ t.length := by
                have := skipComment_hash_len pos1 t
                rw [hcm] at this; simpa using this
              have hcm2 := skipComment_counts pos1 ('#' :: t)
              rw [hcm] at hcm2; simp only [List.length_cons] at hcm2
              have hA : skipComment pos1 ('#' :: (t ++ carry)) = (p2, c2 ++ carry) := by
                have := skipComment_local pos1 ('#' :: t) carry (by simp)
                  (by rw [hcm]; exact hstop)
                rw [hcm] at this; simpa using this
              cases hel : skipEol p2 c2 with
              | mk p3 c3 =>
                have hc3suf : c3 <:+ c2 := by
                  have := skipEol_suffix p2 c2; rw [hel] at this; exact this
                have hel2 := skipEol_counts p2 c2
                rw [hel] at hel2; simp only at hel2
                have hB : skipEol p2 (c2 ++ carry) = (p3, c3 ++ carry) := by
                  have := skipEol_local p2 c2 carry hstop (ne_singleton_cr_of_last hc2last)
                  rw [hel] at this; simpa using this
                rw [hA]; simp only; rw [hB]; simp only
                rw [hcm] at hmid; simp only at hmid
                rw [hel] at hmid; simp only at hmid
                have hEnd : EndsWithNewline c3 := by
                  by_cases hc3 : c3 = []
                  · exact Or.inl hc3
                  · exact Or.inr (getLast?_of_suffix hc3suf hc3 hc2last)
                have hc3len : c3.length ≤ c2.length := hc3suf.length_le
                have hmid' : parseQuadLinesAcc .rdf11 (c3.length + 1) p3 c3 ds = .ok dsMid := by
                  rw [← parseQuadLinesAcc11_fuel_indep complete.length (c3.length + 1) p3 c3 ds
                        (by omega) (by omega)]
                  exact hmid
                have hrec := parseQuadLines11_concat n c3 (by omega) carry p3 f'
                  ds dsMid hEnd (by simp only [List.length_append]; omega) hmid'
                rw [hrec]
                have hpos : p3 + c3.length = pos + complete.length := by omega
                rw [hpos]; exact hRHS
          · by_cases hnl : a = '\n'
            · subst hnl
              have hne : ('\n' :: t) ≠ [] := by simp
              cases hel : skipEol pos1 ('\n' :: t) with
              | mk p2 c2 =>
                have hsuf := skipEol_suffix pos1 ('\n' :: t)
                rw [hel] at hsuf; simp only at hsuf
                have hcnt := skipEol_counts pos1 ('\n' :: t)
                rw [hel] at hcnt; simp only [List.length_cons] at hcnt
                have hlen : c2.length ≤ t.length := by
                  have := skipEol_lf_len pos1 t
                  rw [hel] at this; simpa using this
                have hB : skipEol pos1 ('\n' :: (t ++ carry)) = (p2, c2 ++ carry) := by
                  have := skipEol_local pos1 ('\n' :: t) carry hne
                    (ne_singleton_cr_of_last hlast1)
                  rw [hel] at this; simpa using this
                rw [hB]; simp only
                rw [hel] at hmid; simp only at hmid
                have hEnd : EndsWithNewline c2 := by
                  by_cases hc2 : c2 = []
                  · exact Or.inl hc2
                  · exact Or.inr (getLast?_of_suffix hsuf hc2 hlast1)
                have hmid' : parseQuadLinesAcc .rdf11 (c2.length + 1) p2 c2 ds = .ok dsMid := by
                  rw [← parseQuadLinesAcc11_fuel_indep complete.length (c2.length + 1) p2 c2 ds
                        (by omega) (by omega)]
                  exact hmid
                have hrec := parseQuadLines11_concat n c2 (by omega) carry p2 f'
                  ds dsMid hEnd (by simp only [List.length_append]; omega) hmid'
                rw [hrec]
                have hpos : p2 + c2.length = pos + complete.length := by omega
                rw [hpos]; exact hRHS
            · by_cases hcr : a = '\r'
              · subst hcr
                have hne : ('\r' :: t) ≠ [] := by simp
                cases hel : skipEol pos1 ('\r' :: t) with
                | mk p2 c2 =>
                  have hsuf := skipEol_suffix pos1 ('\r' :: t)
                  rw [hel] at hsuf; simp only at hsuf
                  have hcnt := skipEol_counts pos1 ('\r' :: t)
                  rw [hel] at hcnt; simp only [List.length_cons] at hcnt
                  have hlen : c2.length ≤ t.length := by
                    have := skipEol_cr_len pos1 t
                    rw [hel] at this; simpa using this
                  have hB : skipEol pos1 ('\r' :: (t ++ carry)) = (p2, c2 ++ carry) := by
                    have := skipEol_local pos1 ('\r' :: t) carry hne
                      (ne_singleton_cr_of_last hlast1)
                    rw [hel] at this; simpa using this
                  rw [hB]; simp only
                  rw [hel] at hmid; simp only at hmid
                  have hEnd : EndsWithNewline c2 := by
                    by_cases hc2 : c2 = []
                    · exact Or.inl hc2
                    · exact Or.inr (getLast?_of_suffix hsuf hc2 hlast1)
                  have hmid' : parseQuadLinesAcc .rdf11 (c2.length + 1) p2 c2 ds = .ok dsMid := by
                    rw [← parseQuadLinesAcc11_fuel_indep complete.length (c2.length + 1) p2 c2 ds
                          (by omega) (by omega)]
                    exact hmid
                  have hrec := parseQuadLines11_concat n c2 (by omega) carry p2 f'
                    ds dsMid hEnd (by simp only [List.length_append]; omega) hmid'
                  rw [hrec]
                  have hpos : p2 + c2.length = pos + complete.length := by omega
                  rw [hpos]; exact hRHS
              · -- the statement branch
                split at hmid <;> (try (exfalso; simp_all; done))
                split <;> (try (exfalso; simp_all; done))
                cases hq : readNQuad11 pos1 (a :: t) with
                | error e => rw [hq] at hmid; simp at hmid
                | ok v =>
                  obtain ⟨tr, gg, p2, c2⟩ := v
                  have hdot := readNQuad11_dot pos1 (a :: t) tr gg p2 c2 hq
                  have hc2ne : c2 ≠ [] := by
                    intro hc; subst hc
                    have := getLast?_of_suffix hdot (by simp) hlast1
                    simp at this
                  have hc2last : c2.getLast? = some '\n' :=
                    getLast?_of_suffix ((List.suffix_cons '.' c2).trans hdot) hc2ne hlast1
                  have hqc := readNQuad11_counts pos1 (a :: t) tr gg p2 c2 hq
                  simp only [List.length_cons] at hqc
                  have hqlen : c2.length < t.length + 1 := by
                    have := hdot.length_le; simp at this; omega
                  have hqloc := readNQuad11_local pos1 (a :: t) carry tr gg p2 c2 hq hc2ne
                  rw [List.cons_append] at hqloc
                  rw [hqloc]; simp only
                  rw [hq] at hmid; simp only at hmid
                  have hne3 : (skipWs p2 c2).2 ≠ [] := by
                    have := span_snd_ne_nil_of_last isNtWs c2 '\n' hc2last (by decide)
                    simpa [skipWs] using this
                  have hwloc := skipWs_local p2 c2 carry hne3
                  have hwcnt := skipWs_counts p2 c2
                  have hwsuf := skipWs_suffix p2 c2
                  have hwlast : (skipWs p2 c2).2.getLast? = some '\n' :=
                    getLast?_of_suffix hwsuf hne3 hc2last
                  have hwlen : (skipWs p2 c2).2.length ≤ c2.length := hwsuf.length_le
                  cases hws : skipWs p2 c2 with
                  | mk p3 c3 =>
                    rw [hws] at hne3 hwloc hwcnt hwlast hwlen
                    simp only at hne3 hwloc hwcnt hwlast hwlen
                    rw [hwloc]; simp only
                    rw [hws] at hmid; simp only at hmid
                    have hstop := skipComment_stops p3 c3 hwlast
                    have hcmloc := skipComment_local p3 c3 carry hne3 hstop
                    have hcmcnt := skipComment_counts p3 c3
                    have hcmsuf := skipComment_suffix p3 c3
                    have hcmlast : (skipComment p3 c3).2.getLast? = some '\n' :=
                      getLast?_of_suffix hcmsuf hstop hwlast
                    have hcmlen : (skipComment p3 c3).2.length ≤ c3.length :=
                      hcmsuf.length_le
                    cases hcm : skipComment p3 c3 with
                    | mk p4 c4 =>
                      rw [hcm] at hstop hcmloc hcmcnt hcmlast hcmlen
                      simp only at hstop hcmloc hcmcnt hcmlast hcmlen
                      rw [hcmloc]; simp only
                      rw [hcm] at hmid; simp only at hmid
                      have helloc := skipEol_local p4 c4 carry hstop
                        (ne_singleton_cr_of_last hcmlast)
                      have helcnt := skipEol_counts p4 c4
                      have helsuf := skipEol_suffix p4 c4
                      have hellen : (skipEol p4 c4).2.length ≤ c4.length := helsuf.length_le
                      cases hel : skipEol p4 c4 with
                      | mk p5 c5 =>
                        rw [hel] at helloc helcnt helsuf hellen
                        simp only at helloc helcnt helsuf hellen
                        rw [helloc]; simp only
                        rw [hel] at hmid; simp only at hmid
                        have hEnd : EndsWithNewline c5 := by
                          by_cases hc5 : c5 = []
                          · exact Or.inl hc5
                          · exact Or.inr (getLast?_of_suffix helsuf hc5 hcmlast)
                        have hmid' : parseQuadLinesAcc .rdf11 (c5.length + 1) p5 c5
                            (addQuad ds tr gg) = .ok dsMid := by
                          rw [← parseQuadLinesAcc11_fuel_indep complete.length (c5.length + 1)
                                p5 c5 (addQuad ds tr gg) (by omega) (by omega)]
                          exact hmid
                        have hrec := parseQuadLines11_concat n c5 (by omega) carry p5 f'
                          (addQuad ds tr gg) dsMid hEnd
                          (by simp only [List.length_append]; omega) hmid'
                        rw [hrec]
                        have hpos : p5 + c5.length = pos + complete.length := by omega
                        rw [hpos]; exact hRHS


/-! ## Axiom audit -/

#print axioms skipToEol_stops
#print axioms skipComment_stops
#print axioms parseQuadLines11_concat

end L4Factoidal.Syntax.NQuadsStreaming
