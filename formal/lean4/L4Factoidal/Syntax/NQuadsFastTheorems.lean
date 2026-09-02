/-
L4Factoidal.Syntax.NQuadsFastTheorems — the refinement proof for the
indexed N-Quads accumulator.

`parseNQuadsFast` runs the SAME lexer and the SAME fold
(`foldQuadLinesAcc`) as `parseNQuads`; only the accumulator differs.
This module proves the two agree on every input and every mode:

    parseNQuadsFast s mode = parseNQuads s mode

The argument has three layers.  `FastGraph.Inv` says every bucket holds
exactly the accumulated triples carrying that key, which makes the
bucketed `Triple.eqb` scan decide the same membership question as
`Graph.mem` over the whole graph (`tripleKey` is constant on
`Triple.eqb` classes, so a match can never fall outside the bucket).
`FastDataset.Inv` adds that `namesRev` lists exactly the keys of the
named-graph map and that every stored graph satisfies the graph
invariant, which makes `FastDataset.toDataset` reproduce `addQuad`'s
first-occurrence ordering.  `foldQuadLinesAcc_rel` then transports any
step-wise relation between two consumers through the fold, and the main
theorem instantiates it at `R a b := a.Inv ∧ a.toDataset = b`.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Syntax.NQuadsFast

namespace L4Factoidal.Syntax

open L4Factoidal.RDF
open L4Factoidal.Syntax.NQuadsStreaming

/-! ## Bucket keys -/

/-- `Triple.eqb`-equal triples carry the same bucket key, so a bucket
lookup never hides a match. -/
theorem tripleKey_eq_of_eqb {a b : Triple} (h : Triple.eqb a b = true) :
    tripleKey a = tripleKey b := by
  simp only [Triple.eqb, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hs, hp⟩, ho⟩ := h
  simp only [tripleKey, Prod.mk.injEq]
  exact ⟨Subject.eqb_eq hs, hp, Term.joinKey_eq_of_eqb ho⟩

/-- `Graph.mem` is the `Triple.eqb` scan of the list. -/
theorem graphMem_eq_any (t : Triple) :
    ∀ g : Graph, Graph.mem t g = g.any (fun u => u.eqb t)
  | [] => rfl
  | hd :: tl => by
      simp only [Graph.mem, List.any_cons, graphMem_eq_any t tl]

/-! ## The graph invariant -/

/-- Every bucket holds exactly the accumulated triples with that key. -/
def FastGraph.Inv (g : FastGraph) : Prop :=
  ∀ key, g.buckets.getD key [] = g.rev.filter (fun u => tripleKey u == key)

theorem FastGraph.inv_empty : FastGraph.Inv {} := by
  intro key
  simp

theorem FastGraph.add_inv {g : FastGraph} {t : Triple} (h : g.Inv) :
    (g.add t).Inv := by
  intro key
  simp only [FastGraph.add]
  split
  · exact h key
  · simp only [Std.HashMap.getD_insert, List.filter_cons]
    by_cases hk : (tripleKey t == key) = true
    · have hk' : tripleKey t = key := eq_of_beq hk
      subst hk'
      simp [h (tripleKey t)]
    · simp only [Bool.not_eq_true] at hk
      simp [hk, h key]

/-- The bucket scan and the whole-graph scan answer the same membership
question. -/
theorem FastGraph.bucket_any {g : FastGraph} (t : Triple) (h : g.Inv) :
    (g.buckets.getD (tripleKey t) []).any (fun u => u.eqb t)
      = g.rev.any (fun u => u.eqb t) := by
  rw [h (tripleKey t), Bool.eq_iff_iff]
  simp only [List.any_eq_true, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨u, ⟨hu, -⟩, hp⟩
    exact ⟨u, hu, hp⟩
  · rintro ⟨u, hu, hp⟩
    exact ⟨u, ⟨hu, tripleKey_eq_of_eqb hp⟩, hp⟩

/-- The indexed add refines `Graph.add` on the denoted graph. -/
theorem FastGraph.add_toGraph {g : FastGraph} (t : Triple) (h : g.Inv) :
    (g.add t).toGraph = Graph.add t g.toGraph := by
  have hb := FastGraph.bucket_any t h
  simp only [FastGraph.add, FastGraph.toGraph, Graph.add,
    graphMem_eq_any, List.any_reverse]
  rw [hb]
  split
  · rfl
  · simp

/-! ## The dataset invariant -/

/-- `namesRev` lists exactly the keys of `named`, and every stored graph
satisfies the graph invariant. -/
def FastDataset.Inv (ds : FastDataset) : Prop :=
  ds.default.Inv
  ∧ (∀ name : Subject, (ds.named[name]?).isSome = true ↔ name ∈ ds.namesRev)
  ∧ (∀ (name : Subject) (g : FastGraph), ds.named[name]? = some g → g.Inv)

theorem FastDataset.inv_empty : FastDataset.Inv {} := by
  refine ⟨FastGraph.inv_empty, ?_, ?_⟩
  · intro name; simp
  · intro name g hg; simp at hg

theorem FastDataset.toDataset_empty :
    FastDataset.toDataset {} = Dataset.empty := rfl

/-- `find?` over the denoted named-graph list locates the entry for a
recorded name. -/
theorem find?_map_named (f : Subject → Graph) (name : Subject) :
    ∀ L : List Subject, name ∈ L →
      (L.map (fun n => ({ name := n, graph := f n } : NamedGraph))).find?
          (fun ng => ng.name == name) = some { name := name, graph := f name }
  | [], h => by simp at h
  | n :: rest, h => by
      simp only [List.map_cons, List.find?_cons]
      by_cases hn : n = name
      · subst hn
        simp
      · have hbn : (n == name) = false := by simp [hn]
        simp only [hbn]
        have hrest : name ∈ rest := by
          rcases List.mem_cons.mp h with h1 | h1
          · exact absurd h1.symm hn
          · exact h1
        exact find?_map_named f name rest hrest

theorem find?_map_named_none (f : Subject → Graph) (name : Subject) :
    ∀ L : List Subject, name ∉ L →
      (L.map (fun n => ({ name := n, graph := f n } : NamedGraph))).find?
          (fun ng => ng.name == name) = none
  | [], _ => rfl
  | n :: rest, h => by
      simp only [List.map_cons, List.find?_cons]
      have hn : (n == name) = false := by
        have : n ≠ name := by
          intro hc; exact h (List.mem_cons.mpr (Or.inl hc.symm))
        simp [this]
      simp only [hn]
      exact find?_map_named_none f name rest (fun hc => h (List.mem_cons_of_mem n hc))

theorem FastDataset.add_inv {ds : FastDataset} {t : Triple} {gopt : Option Subject}
    (h : ds.Inv) : (addQuadFast ds t gopt).Inv := by
  obtain ⟨hd, hnames, hgraphs⟩ := h
  cases gopt with
  | none =>
      exact ⟨FastGraph.add_inv hd, hnames, hgraphs⟩
  | some name =>
      simp only [addQuadFast]
      cases hlk : ds.named[name]? with
      | some g =>
          refine ⟨hd, ?_, ?_⟩
          · intro n
            simp only [Std.HashMap.getElem?_insert]
            by_cases hb : (name == n) = true
            · have hb' : name = n := eq_of_beq hb
              subst hb'
              simp only [hb, if_pos, Option.isSome_some, true_iff]
              exact (hnames name).mp (by rw [hlk]; rfl)
            · simp only [Bool.not_eq_true] at hb
              simp only [hb, Bool.false_eq_true, if_false]
              exact hnames n
          · intro n g' hg'
            simp only [Std.HashMap.getElem?_insert] at hg'
            by_cases hb : (name == n) = true
            · simp only [hb, if_pos] at hg'
              cases hg'
              exact FastGraph.add_inv (hgraphs name g hlk)
            · simp only [Bool.not_eq_true] at hb
              simp only [hb, Bool.false_eq_true, if_false] at hg'
              exact hgraphs n g' hg'
      | none =>
          refine ⟨hd, ?_, ?_⟩
          · intro n
            simp only [Std.HashMap.getElem?_insert]
            by_cases hb : (name == n) = true
            · have hb' : name = n := eq_of_beq hb
              subst hb'
              simp
            · simp only [Bool.not_eq_true] at hb
              simp only [hb, Bool.false_eq_true, if_false, List.mem_cons]
              constructor
              · intro hi
                exact Or.inr ((hnames n).mp hi)
              · intro hi
                rcases hi with hi | hi
                · rw [hi] at hb; simp at hb
                · exact (hnames n).mpr hi
          · intro n g' hg'
            simp only [Std.HashMap.getElem?_insert] at hg'
            by_cases hb : (name == n) = true
            · simp only [hb, if_pos] at hg'
              cases hg'
              exact FastGraph.add_inv FastGraph.inv_empty
            · simp only [Bool.not_eq_true] at hb
              simp only [hb, Bool.false_eq_true, if_false] at hg'
              exact hgraphs n g' hg'

/-- The indexed accumulator refines `addQuad` on the denoted dataset. -/
theorem addQuadFast_toDataset {ds : FastDataset} (t : Triple) (gopt : Option Subject)
    (h : ds.Inv) :
    (addQuadFast ds t gopt).toDataset = addQuad ds.toDataset t gopt := by
  obtain ⟨hd, hnames, hgraphs⟩ := h
  cases gopt with
  | none =>
      simp only [addQuadFast, addQuad, FastDataset.toDataset]
      rw [FastGraph.add_toGraph t hd]
  | some name =>
      simp only [addQuadFast]
      cases hlk : ds.named[name]? with
      | some g =>
          have hmem : name ∈ ds.namesRev := (hnames name).mp (by rw [hlk]; rfl)
          have hgetD : ds.named.getD name {} = g := by
            rw [Std.HashMap.getD_eq_getD_getElem?, hlk]; rfl
          have hginv : g.Inv := hgraphs name g hlk
          simp only [FastDataset.toDataset, addQuad]
          rw [find?_map_named (fun n => (ds.named.getD n {}).toGraph) name
                ds.namesRev.reverse (List.mem_reverse.mpr hmem)]
          simp only [List.map_map]
          congr 1
          apply List.map_congr_left
          intro n _
          simp only [Function.comp_apply, Std.HashMap.getD_insert]
          by_cases hb : name = n
          · subst hb
            simp only [beq_self_eq_true, if_true, hgetD]
            rw [FastGraph.add_toGraph t hginv]
          · have hbn : (name == n) = false := by simp [hb]
            have hbn' : (n == name) = false := by simp [Ne.symm hb]
            simp only [hbn, hbn', Bool.false_eq_true, if_false]
      | none =>
          have hmem : name ∉ ds.namesRev := by
            intro hc
            have := (hnames name).mpr hc
            rw [hlk] at this
            simp at this
          simp only [FastDataset.toDataset, addQuad]
          rw [find?_map_named_none (fun n => (ds.named.getD n {}).toGraph) name
                ds.namesRev.reverse (fun hc => hmem (List.mem_reverse.mp hc))]
          simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil]
          congr 1
          congr 1
          · apply List.map_congr_left
            intro n hn
            have hbn : (name == n) = false := by
              have : name ≠ n := by
                intro hc; exact hmem (hc ▸ List.mem_reverse.mp hn)
              simp [this]
            simp only [Std.HashMap.getD_insert, hbn, Bool.false_eq_true, if_false]
          · simp [Std.HashMap.getD_insert_self, FastGraph.add, FastGraph.toGraph]

/-! ## Transporting a step-wise relation through the fold -/

/-- Two parse outcomes agree: the same error, or accumulators in `R`. -/
def ExceptRel {α β : Type} (R : α → β → Prop) :
    Except ParseError α → Except ParseError β → Prop
  | .error e, .error e' => e = e'
  | .ok a, .ok b => R a b
  | _, _ => False

/-- The statement branch of `foldQuadLinesAcc`, unfolded once so the
relational proof does not have to re-split the character matcher. -/
private theorem fold_default_branch (mode : Mode) {α : Type}
    (consume : α → Triple → Option Subject → α)
    (f pos pos1 : Nat) (cs t : List Char) (c : Char) (acc : α)
    (hw : skipWs pos cs = (pos1, c :: t))
    (h1 : c ≠ '#') (h2 : c ≠ '\n') (h3 : c ≠ '\r') :
    foldQuadLinesAcc mode consume (f + 1) pos cs acc
      = (match (match mode with
                | .rdf11 => readNQuad11 pos1 (c :: t)
                | .rdf12 => readNQuad12 pos1 (c :: t)) with
         | .error e => .error e
         | .ok (tr, gopt, pos2, cs2) =>
             let acc' := consume acc tr gopt
             let (pos3, cs3) := skipWs pos2 cs2
             let (pos4, cs4) := skipComment pos3 cs3
             let (pos5, cs5) := skipEol pos4 cs4
             foldQuadLinesAcc mode consume f pos5 cs5 acc') := by
  simp only [foldQuadLinesAcc, hw]
  split
  all_goals (try (exfalso; simp_all; done))
  rfl

theorem foldQuadLinesAcc_rel (mode : Mode) {α β : Type} (R : α → β → Prop)
    (cA : α → Triple → Option Subject → α) (cB : β → Triple → Option Subject → β)
    (hcons : ∀ a b t g, R a b → R (cA a t g) (cB b t g)) :
    ∀ (f pos : Nat) (cs : List Char) (a : α) (b : β), R a b →
      ExceptRel R (foldQuadLinesAcc mode cA f pos cs a)
        (foldQuadLinesAcc mode cB f pos cs b)
  | 0, _, _, _, _, _ => rfl
  | f + 1, pos, cs, a, b, hab => by
      cases hw : skipWs pos cs with
      | mk pos1 cs1 =>
        cases hc1 : cs1 with
        | nil =>
            rw [hc1] at hw
            simp only [foldQuadLinesAcc, hw]
            exact hab
        | cons c t =>
          rw [hc1] at hw
          by_cases hh : c = '#'
          · subst hh
            simp only [foldQuadLinesAcc, hw]
            exact foldQuadLinesAcc_rel mode R cA cB hcons f _ _ _ _ hab
          · by_cases hn : c = '\n'
            · subst hn
              simp only [foldQuadLinesAcc, hw]
              exact foldQuadLinesAcc_rel mode R cA cB hcons f _ _ _ _ hab
            · by_cases hr : c = '\r'
              · subst hr
                simp only [foldQuadLinesAcc, hw]
                exact foldQuadLinesAcc_rel mode R cA cB hcons f _ _ _ _ hab
              · rw [fold_default_branch mode cA f pos pos1 cs t c a hw hh hn hr,
                    fold_default_branch mode cB f pos pos1 cs t c b hw hh hn hr]
                cases hs : (match mode with
                            | .rdf11 => readNQuad11 pos1 (c :: t)
                            | .rdf12 => readNQuad12 pos1 (c :: t)) with
                | error e => rfl
                | ok v =>
                    obtain ⟨tr, gg, p2, c2⟩ := v
                    exact foldQuadLinesAcc_rel mode R cA cB hcons f _ _ _ _
                      (hcons a b tr gg hab)

/-! ## The refinement -/

/-- The indexed N-Quads parser computes exactly the reference parser's
result, on every document and in both modes. -/
theorem parseNQuadsFast_eq_parseNQuads (s : String) (mode : Mode) :
    parseNQuadsFast s mode = parseNQuads s mode := by
  simp only [parseNQuadsFast, parseNQuads, parseQuadLinesAcc_eq_fold]
  have hrel := foldQuadLinesAcc_rel mode
    (fun (a : FastDataset) (b : Dataset) => a.Inv ∧ a.toDataset = b)
    addQuadFast (fun ds t gopt => addQuad ds t gopt)
    (by
      intro a b t g hab
      exact ⟨FastDataset.add_inv hab.1,
        by rw [addQuadFast_toDataset t g hab.1, hab.2]⟩)
    (s.toList.length + 1) 0 s.toList {} Dataset.empty
    ⟨FastDataset.inv_empty, FastDataset.toDataset_empty⟩
  cases hA : foldQuadLinesAcc mode addQuadFast (s.toList.length + 1) 0 s.toList {} with
  | error e =>
      cases hB : foldQuadLinesAcc mode (fun ds t gopt => addQuad ds t gopt)
          (s.toList.length + 1) 0 s.toList Dataset.empty with
      | error e' =>
          rw [hA] at hrel; rw [hB] at hrel
          simp only [ExceptRel] at hrel
          simp [Except.map, hrel]
      | ok d =>
          rw [hA] at hrel; rw [hB] at hrel
          exact absurd hrel (by simp [ExceptRel])
  | ok a =>
      cases hB : foldQuadLinesAcc mode (fun ds t gopt => addQuad ds t gopt)
          (s.toList.length + 1) 0 s.toList Dataset.empty with
      | error e' =>
          rw [hA] at hrel; rw [hB] at hrel
          exact absurd hrel (by simp [ExceptRel])
      | ok d =>
          rw [hA] at hrel; rw [hB] at hrel
          simp only [ExceptRel] at hrel
          simp [Except.map, hrel.2]

/-! ## Axiom audit -/

#print axioms parseNQuadsFast_eq_parseNQuads

end L4Factoidal.Syntax
