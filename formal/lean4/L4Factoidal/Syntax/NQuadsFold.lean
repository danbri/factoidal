/-
L4Factoidal.Syntax.NQuadsFold — the generic N-Quads consumer.

Port of the consumer half of `formal/fstar/RDF.NQuads.Streaming.fst`
(`quad_step` / `feed_chunk_consume` / `stream_consume` /
`batch_consume` / `theorem_stream_consume_eq_batch`): a caller supplies
its own `consume : α → Triple → Option Subject → α` and receives every
quad of the document, chunked or whole, without a `Dataset` being
built.

Per the owner's abstraction steer (CLAUDE.md, Standing decisions,
2026-08-24), the fuel-independence and line-boundary concatenation
proofs are stated ONCE here, over the accumulator type `α`. They are
the proofs from `NQuadsStreaming.lean` / `NQuadsConcat.lean` with
`Dataset` generalised to `α` and `addQuad` to `consume`; those proofs
never inspect the accumulator, so the text is unchanged apart from the
binders. `foldQuadLinesAcc_eq_parse` ties the generic fold back to the
shipping parser, so the dataset instance is the instantiation, not a
second proof.

The recursion threads exactly `(α, carry, pos, err)` between chunks —
the accumulator's own footprint plus at most one partial line. The
fold adds no retention of its own; a consumer that rebuilds the whole
dataset (`addQuad`) grows exactly as batch parsing does.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.Syntax.NQuadsHomomorphism

namespace L4Factoidal.Syntax.NQuadsStreaming
open L4Factoidal.RDF
open L4Factoidal.Syntax

/-! ## The fold

`parseQuadLinesAcc` with the one `Dataset`-specific step abstracted:
`addQuad ds t gopt` becomes `consume acc t gopt`. Same five branches,
same fuel discipline. -/

def foldQuadLinesAcc (mode : Mode) {α : Type}
    (consume : α → Triple → Option Subject → α) :
    Nat → Nat → List Char → α → Except ParseError α
  | 0, pos, _, _ =>
      .error ⟨"internal error: parser fuel exhausted (should be unreachable)", pos⟩
  | fuel' + 1, pos, cs, acc =>
      let (pos1, cs1) := skipWs pos cs
      match cs1 with
      | [] => .ok acc
      | '#' :: _ =>
          let (pos2, cs2) := skipComment pos1 cs1
          let (pos3, cs3) := skipEol pos2 cs2
          foldQuadLinesAcc mode consume fuel' pos3 cs3 acc
      | '\n' :: _ =>
          let (pos2, cs2) := skipEol pos1 cs1
          foldQuadLinesAcc mode consume fuel' pos2 cs2 acc
      | '\r' :: _ =>
          let (pos2, cs2) := skipEol pos1 cs1
          foldQuadLinesAcc mode consume fuel' pos2 cs2 acc
      | _ =>
          let step := match mode with
            | .rdf11 => readNQuad11 pos1 cs1
            | .rdf12 => readNQuad12 pos1 cs1
          match step with
          | .error e => .error e
          | .ok (t, gopt, pos2, cs2) =>
              let acc' := consume acc t gopt
              let (pos3, cs3) := skipWs pos2 cs2
              let (pos4, cs4) := skipComment pos3 cs3
              let (pos5, cs5) := skipEol pos4 cs4
              foldQuadLinesAcc mode consume fuel' pos5 cs5 acc'

/-- The shipping parser IS the fold at `consume = addQuad`. This is the
instantiation that makes the generic proofs cover the dataset case. -/
theorem parseQuadLinesAcc_eq_fold (mode : Mode) :
    ∀ (f pos : Nat) (cs : List Char) (ds : Dataset),
      parseQuadLinesAcc mode f pos cs ds
        = foldQuadLinesAcc mode (fun ds t gopt => addQuad ds t gopt) f pos cs ds
  | 0, _, _, _ => rfl
  | f + 1, pos, cs, ds => by
      simp only [parseQuadLinesAcc, foldQuadLinesAcc]
      cases hw : skipWs pos cs with
      | mk pos1 cs1 =>
        dsimp only
        cases hc1 : cs1 with
        | nil => rfl
        | cons a t =>
          by_cases hh : a = '#'
          · subst hh
            exact parseQuadLinesAcc_eq_fold mode f _ _ _
          · by_cases hn : a = '\n'
            · subst hn
              exact parseQuadLinesAcc_eq_fold mode f _ _ _
            · by_cases hr : a = '\r'
              · subst hr
                exact parseQuadLinesAcc_eq_fold mode f _ _ _
              · -- Case on `mode` first: with the reader call plain,
                -- `simp_all` can use the reader equations. Then split
                -- rounds reduce both sides' compiled matches; the
                -- contradictions close against `hh`/`hn`/`hr`, and the
                -- surviving pair is the recursive call up to beta.
                cases mode
                all_goals (
                  split
                  all_goals (try (exfalso; simp_all; done))
                  all_goals (try split)
                  all_goals (try (exfalso; simp_all; done))
                  all_goals (try split)
                  all_goals (try (exfalso; simp_all; done))
                  all_goals (first
                    | rfl
                    | grind
                    | (exact parseQuadLinesAcc_eq_fold _ f _ _ _)
                    | (simp_all; done)
                    | (simp_all
                       exact parseQuadLinesAcc_eq_fold _ f _ _ _)))

/-! ## Fuel independence, once, over `α` -/

theorem foldQuadLines11_fuel_indep {α : Type} (consume : α → Triple → Option Subject → α) :
    ∀ (f g pos : Nat) (cs : List Char) (ds : α),
      cs.length < f → cs.length < g →
      foldQuadLinesAcc .rdf11 consume f pos cs ds = foldQuadLinesAcc .rdf11 consume g pos cs ds
  | 0, _, _, _, _, hf, _ => absurd hf (by omega)
  | _ + 1, 0, _, _, _, _, hg => absurd hg (by omega)
  | f + 1, g + 1, pos, cs, ds, hf, hg => by
      simp only [foldQuadLinesAcc]
      cases hw : skipWs pos cs with
      | mk pos1 cs1 =>
        have hle1 : cs1.length ≤ cs.length := by
          have := skipWs_len pos cs; rw [hw] at this; exact this
        dsimp only
        cases hc1 : cs1 with
        | nil => rfl
        | cons a t =>
          have hlt : t.length < cs.length := by
            rw [hc1] at hle1; simp at hle1; omega
          by_cases hh : a = '#'
          · subst hh
            have h1 := skipComment_hash_len pos1 t
            have h2 := skipEol_len (skipComment pos1 ('#' :: t)).1
                         (skipComment pos1 ('#' :: t)).2
            refine foldQuadLines11_fuel_indep consume f g _ _ _ ?_ ?_ <;> omega
          · by_cases hn : a = '\n'
            · subst hn
              have h2 := skipEol_lf_len pos1 t
              refine foldQuadLines11_fuel_indep consume f g _ _ _ ?_ ?_ <;> omega
            · by_cases hr : a = '\r'
              · subst hr
                have h2 := skipEol_cr_len pos1 t
                refine foldQuadLines11_fuel_indep consume f g _ _ _ ?_ ?_ <;> omega
              · split
                all_goals (try (exfalso; simp_all; done))
                split
                · rfl
                · rename_i tr gg p2 c2 heq
                  have hlen := readNQuad11_len pos1 (a :: t) tr gg p2 c2 heq
                  have hA : (skipWs p2 c2).2.length ≤ c2.length := skipWs_len p2 c2
                  have hB : (skipComment (skipWs p2 c2).1 (skipWs p2 c2).2).2.length
                      ≤ (skipWs p2 c2).2.length := skipComment_len _ _
                  have hC : (skipEol
                        (skipComment (skipWs p2 c2).1 (skipWs p2 c2).2).1
                        (skipComment (skipWs p2 c2).1 (skipWs p2 c2).2).2).2.length
                      ≤ (skipComment (skipWs p2 c2).1 (skipWs p2 c2).2).2.length :=
                    skipEol_len _ _
                  simp at hlen
                  refine foldQuadLines11_fuel_indep consume f g _ _ _ ?_ ?_ <;> omega


/-! ## The concatenation lemma, once, over `α` -/

private theorem foldConcat_nil {α : Type} (consume : α → Triple → Option Subject → α)
    (carry : List Char) (pos f : Nat) (ds dsMid : α)
    (hf : carry.length < f)
    (hmid : foldQuadLinesAcc .rdf11 consume 1 pos [] ds = .ok dsMid) :
    foldQuadLinesAcc .rdf11 consume f pos carry ds
      = foldQuadLinesAcc .rdf11 consume (carry.length + 1) pos carry dsMid := by
  have hds : dsMid = ds := by
    simp [foldQuadLinesAcc, skipWs, List.span, List.span.loop] at hmid
    exact hmid.symm
  subst hds
  exact foldQuadLines11_fuel_indep consume f (carry.length + 1) pos carry dsMid
    (by omega) (by omega)



theorem foldQuadLines11_concat {α : Type} (consume : α → Triple → Option Subject → α) :
    ∀ (n : Nat) (complete : List Char), complete.length ≤ n →
    ∀ (carry : List Char) (pos f : Nat) (ds dsMid : α),
      EndsWithNewline complete →
      (complete ++ carry).length < f →
      foldQuadLinesAcc .rdf11 consume (complete.length + 1) pos complete ds = .ok dsMid →
      foldQuadLinesAcc .rdf11 consume f pos (complete ++ carry) ds
        = foldQuadLinesAcc .rdf11 consume (carry.length + 1) (pos + complete.length) carry dsMid
  | 0, complete, hn, carry, pos, f, ds, dsMid, _, hf, hmid => by
      have hnil : complete = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hnil
      simp only [List.nil_append, List.length_nil, Nat.add_zero] at *
      exact foldConcat_nil consume carry pos f ds dsMid (by omega) hmid
  | n + 1, complete, hn, carry, pos, f, ds, dsMid, hend, hf, hmid => by
    rcases hend with hnil | hlastC
    · subst hnil
      simp only [List.nil_append, List.length_nil, Nat.add_zero] at *
      exact foldConcat_nil consume carry pos f ds dsMid (by omega) hmid
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
          foldQuadLinesAcc .rdf11 consume (carry.length + 1) (pos + complete.length) carry dsMid = RHS
        simp only [foldQuadLinesAcc] at hmid ⊢
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
                have hmid' : foldQuadLinesAcc .rdf11 consume (c3.length + 1) p3 c3 ds = .ok dsMid := by
                  rw [← foldQuadLines11_fuel_indep consume complete.length (c3.length + 1) p3 c3 ds
                        (by omega) (by omega)]
                  exact hmid
                have hrec := foldQuadLines11_concat consume n c3 (by omega) carry p3 f'
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
                have hmid' : foldQuadLinesAcc .rdf11 consume (c2.length + 1) p2 c2 ds = .ok dsMid := by
                  rw [← foldQuadLines11_fuel_indep consume complete.length (c2.length + 1) p2 c2 ds
                        (by omega) (by omega)]
                  exact hmid
                have hrec := foldQuadLines11_concat consume n c2 (by omega) carry p2 f'
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
                  have hmid' : foldQuadLinesAcc .rdf11 consume (c2.length + 1) p2 c2 ds = .ok dsMid := by
                    rw [← foldQuadLines11_fuel_indep consume complete.length (c2.length + 1) p2 c2 ds
                          (by omega) (by omega)]
                    exact hmid
                  have hrec := foldQuadLines11_concat consume n c2 (by omega) carry p2 f'
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
                        have hmid' : foldQuadLinesAcc .rdf11 consume (c5.length + 1) p5 c5
                            (consume ds tr gg) = .ok dsMid := by
                          rw [← foldQuadLines11_fuel_indep consume complete.length (c5.length + 1)
                                p5 c5 (consume ds tr gg) (by omega) (by omega)]
                          exact hmid
                        have hrec := foldQuadLines11_concat consume n c5 (by omega) carry p5 f'
                          (consume ds tr gg) dsMid hEnd
                          (by simp only [List.length_append]; omega) hmid'
                        rw [hrec]
                        have hpos : p5 + c5.length = pos + complete.length := by omega
                        rw [hpos]; exact hRHS



/-! ## The chunked consumer -/

structure StreamStateC (α : Type) where
  acc : α
  carry : List Char
  pos : Nat
  err : Option ParseError

def initialStateC {α : Type} (init : α) : StreamStateC α :=
  { acc := init, carry := [], pos := 0, err := none }

def foldFrom (mode : Mode) {α : Type}
    (consume : α → Triple → Option Subject → α)
    (pos : Nat) (cs : List Char) (acc : α) : Except ParseError α :=
  foldQuadLinesAcc mode consume (cs.length + 1) pos cs acc

def feedChunkC (mode : Mode) {α : Type}
    (consume : α → Triple → Option Subject → α)
    (st : StreamStateC α) (chunk : List Char) : StreamStateC α :=
  match st.err with
  | some _ => st
  | none =>
      let buf := st.carry ++ chunk
      let (complete, carry) := splitCompleteLines buf
      match foldFrom mode consume st.pos complete st.acc with
      | .ok acc' =>
          { acc := acc', carry := carry, pos := st.pos + complete.length, err := none }
      | .error e =>
          { acc := st.acc, carry := carry, pos := st.pos + complete.length,
            err := some e }

def finishC (mode : Mode) {α : Type}
    (consume : α → Triple → Option Subject → α)
    (st : StreamStateC α) : Except ParseError α :=
  match st.err with
  | some e => .error e
  | none => foldFrom mode consume st.pos st.carry st.acc

def streamConsume (mode : Mode) {α : Type}
    (consume : α → Triple → Option Subject → α)
    (init : α) (chunks : List (List Char)) : Except ParseError α :=
  finishC mode consume (chunks.foldl (feedChunkC mode consume) (initialStateC init))

def batchConsume (mode : Mode) {α : Type}
    (consume : α → Triple → Option Subject → α)
    (init : α) (doc : List Char) : Except ParseError α :=
  foldFrom mode consume 0 doc init

/-! ## Streaming agrees with batch, for every consumer -/

theorem feedChunkC_error_sticky (mode : Mode) {α : Type}
    (consume : α → Triple → Option Subject → α)
    (st : StreamStateC α) (chunk : List Char)
    (e : ParseError) (h : st.err = some e) :
    feedChunkC mode consume st chunk = st := by
  simp only [feedChunkC, h]

theorem foldlC_err_sticky {α : Type}
    (consume : α → Triple → Option Subject → α) :
    ∀ (chunks : List (List Char)) (st : StreamStateC α)
    (e : ParseError), st.err = some e →
    (chunks.foldl (feedChunkC .rdf11 consume) st).err = some e
  | [], st, e, h => h
  | c :: rest, st, e, h => by
      simp only [List.foldl_cons]
      rw [feedChunkC_error_sticky .rdf11 consume st c e h]
      exact foldlC_err_sticky consume rest st e h

theorem foldlC_inv {α : Type} (consume : α → Triple → Option Subject → α) (init : α) :
    ∀ (chunks : List (List Char)) (st : StreamStateC α)
    (consumed : List Char),
      st.err = none → st.pos = consumed.length → EndsWithNewline consumed →
      foldFrom .rdf11 consume 0 consumed init = .ok st.acc →
      (chunks.foldl (feedChunkC .rdf11 consume) st).err = none →
      ∃ consumed',
        consumed' ++ (chunks.foldl (feedChunkC .rdf11 consume) st).carry
          = consumed ++ st.carry ++ chunks.flatten ∧
        (chunks.foldl (feedChunkC .rdf11 consume) st).pos = consumed'.length ∧
        EndsWithNewline consumed' ∧
        foldFrom .rdf11 consume 0 consumed' init
          = .ok (chunks.foldl (feedChunkC .rdf11 consume) st).acc
  | [], st, consumed, herr, hpos, hend, hds, _ => by
      exact ⟨consumed, by simp, hpos, hend, hds⟩
  | c :: rest, st, consumed, herr, hpos, hend, hds, hfinal => by
      simp only [List.foldl_cons] at hfinal ⊢
      cases hp : foldFrom .rdf11 consume st.pos (splitCompleteLines (st.carry ++ c)).1 st.acc with
      | error e =>
          exfalso
          have hse : (feedChunkC .rdf11 consume st c).err = some e := by
            simp only [feedChunkC, herr, hp]
          rw [foldlC_err_sticky consume rest _ e hse] at hfinal
          simp at hfinal
      | ok ds' =>
          have hst' : feedChunkC .rdf11 consume st c
              = { acc := ds', carry := (splitCompleteLines (st.carry ++ c)).2,
                  pos := st.pos + (splitCompleteLines (st.carry ++ c)).1.length,
                  err := none } := by
            simp only [feedChunkC, herr, hp]
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
          have hnew : foldFrom .rdf11 consume 0
              (consumed ++ (splitCompleteLines (st.carry ++ c)).1) init = .ok ds' := by
            simp only [foldFrom] at hds hp ⊢
            rw [foldQuadLines11_concat consume consumed.length consumed (by omega)
                  (splitCompleteLines (st.carry ++ c)).1 0
                  ((consumed ++ (splitCompleteLines (st.carry ++ c)).1).length + 1)
                  init st.acc hend (by simp) hds]
            rw [Nat.zero_add, ← hpos]
            exact hp
          have := foldlC_inv consume init rest (feedChunkC .rdf11 consume st c)
            (consumed ++ (splitCompleteLines (st.carry ++ c)).1)
            (by rw [hst']) (by rw [hst']; simp; omega)
            (endsWithNewline_append _ _ hend hcompEnd) (by rw [hst']; exact hnew) hfinal
          obtain ⟨cc, h1, h2, h3, h4⟩ := this
          refine ⟨cc, ?_, h2, h3, h4⟩
          rw [h1, hst']
          simp only [List.append_assoc, hrec]
          simp

theorem streamConsume11_eq_batch {α : Type}
    (consume : α → Triple → Option Subject → α) (init : α)
    (chunks : List (List Char)) (r : α)
    (h : streamConsume .rdf11 consume init chunks = .ok r) :
    foldFrom .rdf11 consume 0 chunks.flatten init = .ok r := by
  simp only [streamConsume, finishC] at h
  cases hE : (chunks.foldl (feedChunkC .rdf11 consume) (initialStateC init)).err with
  | some e => rw [hE] at h; simp at h
  | none =>
      rw [hE] at h
      simp only at h
      obtain ⟨cc, h1, h2, h3, h4⟩ :=
        foldlC_inv consume init chunks (initialStateC init) [] rfl rfl (Or.inl rfl)
          (by simp [foldFrom, initialStateC, foldQuadLinesAcc, skipWs, List.span,
                    List.span.loop]) hE
      have h1' : cc ++ (chunks.foldl (feedChunkC .rdf11 consume) (initialStateC init)).carry
          = chunks.flatten := by rw [h1]; simp [initialStateC]
      simp only [foldFrom] at h h4 ⊢
      rw [← h1']
      rw [foldQuadLines11_concat consume cc.length cc (by omega)
            (chunks.foldl (feedChunkC .rdf11 consume) (initialStateC init)).carry 0
            ((cc ++ (chunks.foldl (feedChunkC .rdf11 consume) (initialStateC init)).carry).length + 1)
            init (chunks.foldl (feedChunkC .rdf11 consume) (initialStateC init)).acc h3 (by simp) h4]
      rw [Nat.zero_add, ← h2]
      exact h


/-- `batchConsume` unfolded, for callers that state the batch side
directly. -/
theorem batchConsume_def (mode : Mode) {α : Type}
    (consume : α → Triple → Option Subject → α) (init : α) (doc : List Char) :
    batchConsume mode consume init doc
      = foldQuadLinesAcc mode consume (doc.length + 1) 0 doc init := rfl


/-! ## Build-time checks

A counting consumer — the shape the F\* module's `stream_consume` exists
for — run chunked and whole, against the dataset path on the same
input. Chunk boundaries fall mid-line on purpose. -/

private def countQ : Nat → Triple → Option Subject → Nat := fun n _ _ => n + 1
private def l1 : List Char := "<a:1> <a:p> <a:2> .\n".toList
private def l2 : List Char := "<a:2> <a:p> <a:3> _:g .\n".toList
private def doc2 : List Char := l1 ++ l2

private def okCount (r : Except ParseError Nat) : Nat :=
  match r with | .ok n => n | .error _ => 0

#guard okCount (batchConsume .rdf11 countQ 0 doc2) == 2
#guard okCount (streamConsume .rdf11 countQ 0 [doc2.take 8, doc2.drop 8]) == 2
#guard okCount (streamConsume .rdf11 countQ 0 [doc2.take 3, (doc2.drop 3).take 19, doc2.drop 22]) == 2
#guard okCount (streamConsume .rdf11 countQ 0 [l1, l2]) == 2
#guard okCount (streamConsume .rdf11 countQ 0 []) == 0

/-! The graph-label slot reaches the consumer. -/
#guard (match batchConsume .rdf11 (fun acc _ g => acc + (if g.isSome then 1 else 0)) 0 doc2 with
        | .ok n => n | .error _ => 99) == 1

/-! ## Axiom audit -/


#print axioms parseQuadLinesAcc_eq_fold
#print axioms foldQuadLines11_fuel_indep
#print axioms foldQuadLines11_concat
#print axioms foldlC_inv
#print axioms streamConsume11_eq_batch

end L4Factoidal.Syntax.NQuadsStreaming
