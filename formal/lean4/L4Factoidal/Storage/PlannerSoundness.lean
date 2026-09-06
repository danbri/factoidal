/-
L4Factoidal.Storage.PlannerSoundness — the storage half of the
planner-soundness theorem
(`docs/designissues/2026-09-06-planner-soundness-theorem.md`).

`SPARQL/DatasetRestriction.lean` proves the evaluator half: a fragment
query answers the same over a restricted dataset as over the whole one.
This module turns that into the statement the design record asks for —
that reading only the manifest entries
`ShardManifest.quadEntriesForQueryWithKeys` keeps answers the query as
if every entry had been read — by

* naming the canonical restriction of a dataset (`restrictDataset`) and
  proving it satisfies `DatasetRestricted`;
* composing the evaluator theorem TWICE, once for each of the two
  entry sets, so the only storage obligation left is an equality
  between two RESTRICTED datasets rather than between two answers.

## Why the composition takes that shape

The design record's section 3 states the restriction as
`D S = restrictPred P (D E)`. That is not what the planner produces: an
entry the planner KEEPS may still hold rows the restriction drops — a
block selected by its predicate carries rows whose subject lies outside
the query's zone bounds, and they are read. `D S` is therefore a dataset
BETWEEN `restrict keep (D E)` and `D E`, not the restriction itself.

The repair is to apply the evaluator theorem to each side:

```
eval Q (D S) = eval Q (restrict keep (D S))
             = eval Q (restrict keep (D E))     -- the storage obligation
             = eval Q (D E)
```

so the storage side has to prove an equality of DATASETS, which is a
statement about which quads survive, and never mentions the evaluator.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.SPARQL.DatasetRestriction
import L4Factoidal.Storage.ShardManifest

namespace L4Factoidal.Storage.PlannerSoundness

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.StoreDataset
open L4Factoidal.SPARQL.StorePlan
open L4Factoidal.SPARQL.DatasetRestriction

/-! ## 1. The canonical restriction -/

def restrictDataset (keep : Triple → Bool) (d : Dataset) : Dataset :=
  { default := d.default.filter keep
  , named := restrictNamed keep d.named }

/-- No two named graphs share a key. `Storage/QuadDataset.lean`'s
`datasetOfQuads` gives this: it records each graph name once, at its first
occurrence. -/
def distinctNames : List NamedGraph → Prop
  | [] => True
  | ng :: rest => (∀ x ∈ rest, ngKey x ≠ ngKey ng) ∧ distinctNames rest

theorem lookupGraph_none_of_keys (n : Iri) :
    ∀ l : List NamedGraph, (∀ x ∈ l, ngKey x ≠ n) → lookupGraph l n = none
  | [], _ => rfl
  | ng :: rest, h => by
      simp only [lookupGraph]
      rw [if_neg (by
        intro hk
        exact h ng List.mem_cons_self (by simpa using hk))]
      exact lookupGraph_none_of_keys n rest (fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem restrictNamed_keys {keep : Triple → Bool} (n : Iri) :
    ∀ l : List NamedGraph, (∀ x ∈ l, ngKey x ≠ n) →
      ∀ x ∈ restrictNamed keep l, ngKey x ≠ n
  | [], _ => by intro x hx; simp [restrictNamed] at hx
  | ng :: rest, h => by
      intro x hx
      rw [restrictNamed_cons] at hx
      split at hx
      · exact restrictNamed_keys n rest
          (fun y hy => h y (List.mem_cons_of_mem _ hy)) x hx
      · rcases List.mem_cons.mp hx with hx | hx
        · rw [hx, ngKey_graph]
          exact h ng List.mem_cons_self
        · exact restrictNamed_keys n rest
            (fun y hy => h y (List.mem_cons_of_mem _ hy)) x hx

theorem lookupGraph_cons_pos {ng : NamedGraph} {rest : List NamedGraph} {n : Iri}
    (hk : ngKey ng = n) : lookupGraph (ng :: rest) n = some ng.graph := by
  simp only [lookupGraph]
  rw [if_pos (show ((ngKey ng == n) = true) by simp [hk])]

theorem lookupGraph_cons_neg {ng : NamedGraph} {rest : List NamedGraph} {n : Iri}
    (hk : ¬ ngKey ng = n) : lookupGraph (ng :: rest) n = lookupGraph rest n := by
  simp only [lookupGraph]
  rw [if_neg (show ¬((ngKey ng == n) = true) by simpa using hk)]

/-- The named-graph half of `DatasetRestricted`, for the canonical
restriction. -/
theorem lookupGraph_restrictNamed (keep : Triple → Bool) (n : Iri) :
    ∀ l : List NamedGraph, distinctNames l →
      lookupGraph (restrictNamed keep l) n
          = (lookupGraph l n).map (fun g => g.filter keep)
      ∨ (lookupGraph (restrictNamed keep l) n = none ∧
         ∀ g, lookupGraph l n = some g → g.filter keep = [])
  | [], _ => Or.inl rfl
  | ng :: rest, hdist => by
      rw [restrictNamed_cons]
      by_cases hk : ngKey ng = n
      · have hlook : lookupGraph (ng :: rest) n = some ng.graph := lookupGraph_cons_pos hk
        have hnone : lookupGraph (restrictNamed keep rest) n = none := by
          refine lookupGraph_none_of_keys n _ (restrictNamed_keys n rest ?_)
          intro x hx hkx
          exact hdist.1 x hx (by rw [hkx, ← hk])
        by_cases hz : (ng.graph.filter keep).isEmpty = true
        · refine Or.inr ⟨by rw [if_pos hz]; exact hnone, ?_⟩
          intro g hg
          rw [hlook] at hg
          rw [← Option.some.inj hg]
          exact List.isEmpty_iff.mp hz
        · refine Or.inl ?_
          rw [if_neg hz, hlook,
            lookupGraph_cons_pos (ng := { ng with graph := ng.graph.filter keep })
              (rest := restrictNamed keep rest) (by rw [ngKey_graph]; exact hk)]
          rfl
      · rw [lookupGraph_cons_neg hk]
        by_cases hz : (ng.graph.filter keep).isEmpty = true
        · rw [if_pos hz]
          exact lookupGraph_restrictNamed keep n rest hdist.2
        · rw [if_neg hz,
            lookupGraph_cons_neg (ng := { ng with graph := ng.graph.filter keep })
              (rest := restrictNamed keep rest) (by rw [ngKey_graph]; exact hk)]
          exact lookupGraph_restrictNamed keep n rest hdist.2

/-- **The canonical restriction satisfies the relation.** -/
theorem datasetRestricted_restrictDataset (keep : Triple → Bool)
    (readable : Option (List WfIri)) (d : Dataset)
    (hdist : distinctNames d.named) (hne : ∀ ng ∈ d.named, ng.graph ≠ []) :
    DatasetRestricted keep readable d (restrictDataset keep d) :=
  { dflt := rfl
  , named := fun i _ => lookupGraph_restrictNamed keep i.val d.named hdist
  , namedList := fun _ => rfl
  , noEmpty := hne }

/-! ## 2. The composition -/

/-- **Planner soundness for SELECT.** `dE` is the dataset every manifest entry
denotes, `dS` the dataset the entries the planner keeps denote. The storage
obligation is `hagree`: the two datasets carry the same quads once the
restriction is applied — which is what "a skipped entry cannot contribute a
row" says, with no evaluator in it. -/
theorem plannerSoundnessSelect (env : EvalEnv) {keep : Triple → Bool}
    {readable : Option (List WfIri)} {dE dS : Dataset} (q : Query)
    (hdistE : distinctNames dE.named) (hneE : ∀ ng ∈ dE.named, ng.graph ≠ [])
    (hdistS : distinctNames dS.named) (hneS : ∀ ng ∈ dS.named, ng.graph ≠ [])
    (hagree : restrictDataset keep dS = restrictDataset keep dE)
    (hf : plannerFragment q.pattern.rewriteBnodes = true)
    (hk : PatternKept keep q.pattern.rewriteBnodes)
    (hn : ∀ i ∈ graphNamesIn q.pattern.rewriteBnodes, readableName readable i)
    (hv : graphVarIn q.pattern.rewriteBnodes = true → readable = none) :
    runSelectQueryBackendDataset env q (indexedDatasetBackend dS)
      = runSelectQueryBackendDataset env q (indexedDatasetBackend dE) := by
  have hS := runSelectQueryBackendDataset_restrict env
    (datasetRestricted_restrictDataset keep readable dS hdistS hneS) q hf hk hn hv
  have hE := runSelectQueryBackendDataset_restrict env
    (datasetRestricted_restrictDataset keep readable dE hdistE hneE) q hf hk hn hv
  rw [← hS, ← hE, hagree]

/-- **Planner soundness for ASK.** -/
theorem plannerSoundnessAsk (env : EvalEnv) {keep : Triple → Bool}
    {readable : Option (List WfIri)} {dE dS : Dataset} (q : Query)
    (hdistE : distinctNames dE.named) (hneE : ∀ ng ∈ dE.named, ng.graph ≠ [])
    (hdistS : distinctNames dS.named) (hneS : ∀ ng ∈ dS.named, ng.graph ≠ [])
    (hagree : restrictDataset keep dS = restrictDataset keep dE)
    (hf : plannerFragment q.pattern.rewriteBnodes = true)
    (hk : PatternKept keep q.pattern.rewriteBnodes)
    (hn : ∀ i ∈ graphNamesIn q.pattern.rewriteBnodes, readableName readable i)
    (hv : graphVarIn q.pattern.rewriteBnodes = true → readable = none) :
    runAskQueryBackendDataset env q (indexedDatasetBackend dS)
      = runAskQueryBackendDataset env q (indexedDatasetBackend dE) := by
  have hS := runAskQueryBackendDataset_restrict env
    (datasetRestricted_restrictDataset keep readable dS hdistS hneS) q hf hk hn hv
  have hE := runAskQueryBackendDataset_restrict env
    (datasetRestricted_restrictDataset keep readable dE hdistE hneE) q hf hk hn hv
  rw [← hS, ← hE, hagree]

/-! ## 3. The predicate collector establishes `PatternKept`

`keepPred P` is the restriction the predicate collector justifies: keep the
triples whose predicate is in `P`. What has to be shown is that a pattern the
collector admits presents only bounds this restriction keeps, which is the
`PatternKept` hypothesis of the evaluator theorem. -/

def keepPred (P : List WfIri) (t : Triple) : Bool := P.contains t.p

theorem tpKept_of_constPred {P : List WfIri} {tp : TriplePattern} {pred : WfIri}
    (hp : tp.p = .iri pred) (hm : P.contains pred = true) : TpKept (keepPred P) tp := by
  intro mu t hb
  simp only [boundMatches, patternBoundFor, boundPredicateOfPattern, hp,
    Bool.and_eq_true] at hb
  have heq : pred = t.p := Subtype.ext (by simpa using hb.1.2)
  simp only [keepPred, ← heq, hm]

theorem TpKept_mono {keep keep' : Triple → Bool}
    (h : ∀ t, keep t = true → keep' t = true) {tp : TriplePattern} :
    TpKept keep tp → TpKept keep' tp :=
  fun hk mu t hb => h t (hk mu t hb)

theorem PatternKept_mono {keep keep' : Triple → Bool}
    (h : ∀ t, keep t = true → keep' t = true) :
    ∀ p : QueryPattern, PatternKept keep p → PatternKept keep' p
  | .bgp [], hk => fun t => h t (hk t)
  | .bgp (tp :: rest), hk => fun x hx => TpKept_mono h (hk x hx)
  | .empty, hk => fun t => h t (hk t)
  | .join a b, hk =>
      ⟨PatternKept_mono h a hk.1, PatternKept_mono h b hk.2⟩
  | .union a b, hk =>
      ⟨PatternKept_mono h a hk.1, PatternKept_mono h b hk.2⟩
  | .minus a b, hk =>
      ⟨PatternKept_mono h a hk.1, PatternKept_mono h b hk.2⟩
  | .leftJoin a b _, hk =>
      ⟨PatternKept_mono h a hk.1, PatternKept_mono h b hk.2⟩
  | .filter _ p, hk => PatternKept_mono h p hk
  | .bind _ _ p, hk => PatternKept_mono h p hk
  | .graph _ p, hk => PatternKept_mono h p hk
  | .lateral _ _, _ => trivial
  | .values _ _, _ => trivial
  | .service _ _ _, _ => trivial
  | .serviceVar _ _ _, _ => trivial
  | .subSelect _, _ => trivial
  | .propertyPath _ _ _, _ => trivial

theorem keepPred_mono_append_left (P Q : List WfIri) :
    ∀ t, keepPred P t = true → keepPred (P ++ Q) t = true := by
  intro t h
  simp only [keepPred, List.contains_append, Bool.or_eq_true]
  exact Or.inl h

theorem keepPred_mono_append_right (P Q : List WfIri) :
    ∀ t, keepPred Q t = true → keepPred (P ++ Q) t = true := by
  intro t h
  simp only [keepPred, List.contains_append, Bool.or_eq_true]
  exact Or.inr h

/-- The fold `quadNativeConstantPredicates?` runs over a BGP. -/
def predsOf (ps : Bgp) : Option (List WfIri) :=
  ps.foldr (fun pattern rest => do
    let predicates ← rest
    match pattern.p with
    | .iri predicate => some (predicate :: predicates)
    | _ => none) (some [])

theorem predsOf_cons (tp : TriplePattern) (rest : Bgp) :
    predsOf (tp :: rest)
      = (do
          let preds ← predsOf rest
          match tp.p with
          | .iri predicate => some (predicate :: preds)
          | _ => none) := rfl

theorem quadNativeConstantPredicates_bgp (ps : Bgp) :
    ShardManifest.quadNativeConstantPredicates? (.bgp ps)
      = if ps.isEmpty then none else predsOf ps := by
  cases ps <;> rfl

theorem predsOf_mem : ∀ (ps : Bgp) (P : List WfIri), predsOf ps = some P →
    ∀ tp ∈ ps, ∃ pred, tp.p = .iri pred ∧ P.contains pred = true
  | [], P, h => by
      intro _tp htp
      simp at htp
  | tp :: rest, P, h => by
      intro x hx
      rw [predsOf_cons] at h
      cases hr : predsOf rest with
      | none => rw [hr] at h; simp at h
      | some P' =>
          rw [hr] at h
          simp only [bind, Option.bind] at h
          cases hp : tp.p with
          | iri pred =>
              rw [hp] at h
              simp only [Option.some.injEq] at h
              subst h
              rcases List.mem_cons.mp hx with hx | hx
              · exact ⟨pred, by rw [hx, hp], by simp⟩
              · obtain ⟨q, hq1, hq2⟩ := predsOf_mem rest P' hr x hx
                exact ⟨q, hq1, by simp only [List.contains_cons, Bool.or_eq_true]; exact Or.inr hq2⟩
          | var _ => rw [hp] at h; simp at h
          | bnode _ => rw [hp] at h; simp at h
          | literal _ => rw [hp] at h; simp at h
          | tripleTerm _ _ _ => rw [hp] at h; simp at h

/-- **The predicate collector's guarantee.** -/
theorem patternKept_of_quadPredicates :
    ∀ (p : QueryPattern) (P : List WfIri),
      ShardManifest.quadNativeConstantPredicates? p = some P → PatternKept (keepPred P) p
  | .bgp ps, P, h => by
      rw [quadNativeConstantPredicates_bgp] at h
      cases hps : ps with
      | nil => rw [hps] at h; simp at h
      | cons tp rest =>
          rw [hps] at h
          simp only [List.isEmpty_cons, Bool.false_eq_true, if_false] at h
          intro x hx
          obtain ⟨pred, h1, h2⟩ := predsOf_mem (tp :: rest) P h x hx
          exact tpKept_of_constPred h1 h2
  | .join a b, P, h => by
      simp only [ShardManifest.quadNativeConstantPredicates?] at h
      cases ha : ShardManifest.quadNativeConstantPredicates? a with
      | none => rw [ha] at h; simp at h
      | some l =>
          cases hb : ShardManifest.quadNativeConstantPredicates? b with
          | none => rw [ha, hb] at h; simp at h
          | some r =>
              rw [ha, hb] at h
              simp only [bind, Option.bind, Option.some.injEq] at h
              subst h
              exact ⟨PatternKept_mono (keepPred_mono_append_left l r) a
                       (patternKept_of_quadPredicates a l ha),
                     PatternKept_mono (keepPred_mono_append_right l r) b
                       (patternKept_of_quadPredicates b r hb)⟩
  | .union a b, P, h => by
      simp only [ShardManifest.quadNativeConstantPredicates?] at h
      cases ha : ShardManifest.quadNativeConstantPredicates? a with
      | none => rw [ha] at h; simp at h
      | some l =>
          cases hb : ShardManifest.quadNativeConstantPredicates? b with
          | none => rw [ha, hb] at h; simp at h
          | some r =>
              rw [ha, hb] at h
              simp only [bind, Option.bind, Option.some.injEq] at h
              subst h
              exact ⟨PatternKept_mono (keepPred_mono_append_left l r) a
                       (patternKept_of_quadPredicates a l ha),
                     PatternKept_mono (keepPred_mono_append_right l r) b
                       (patternKept_of_quadPredicates b r hb)⟩
  | .minus a b, P, h => by
      simp only [ShardManifest.quadNativeConstantPredicates?] at h
      cases ha : ShardManifest.quadNativeConstantPredicates? a with
      | none => rw [ha] at h; simp at h
      | some l =>
          cases hb : ShardManifest.quadNativeConstantPredicates? b with
          | none => rw [ha, hb] at h; simp at h
          | some r =>
              rw [ha, hb] at h
              simp only [bind, Option.bind, Option.some.injEq] at h
              subst h
              exact ⟨PatternKept_mono (keepPred_mono_append_left l r) a
                       (patternKept_of_quadPredicates a l ha),
                     PatternKept_mono (keepPred_mono_append_right l r) b
                       (patternKept_of_quadPredicates b r hb)⟩
  | .leftJoin a b c, P, h => by
      simp only [ShardManifest.quadNativeConstantPredicates?] at h
      split at h
      · cases ha : ShardManifest.quadNativeConstantPredicates? a with
        | none => rw [ha] at h; simp at h
        | some l =>
            cases hb : ShardManifest.quadNativeConstantPredicates? b with
            | none => rw [ha, hb] at h; simp at h
            | some r =>
                rw [ha, hb] at h
                simp only [bind, Option.bind, Option.some.injEq] at h
                subst h
                exact ⟨PatternKept_mono (keepPred_mono_append_left l r) a
                         (patternKept_of_quadPredicates a l ha),
                       PatternKept_mono (keepPred_mono_append_right l r) b
                         (patternKept_of_quadPredicates b r hb)⟩
      · simp at h
  | .filter c p, P, h => by
      simp only [ShardManifest.quadNativeConstantPredicates?] at h
      split at h
      · exact patternKept_of_quadPredicates p P h
      · simp at h
  | .bind _ _ p, P, h => by
      simp only [ShardManifest.quadNativeConstantPredicates?] at h
      split at h
      · exact patternKept_of_quadPredicates p P h
      · simp at h
  | .graph n p, P, h => by
      simp only [ShardManifest.quadNativeConstantPredicates?] at h
      exact patternKept_of_quadPredicates p P h
  | .propertyPath _ _ _, _, _ => trivial
  | .lateral _ _, _, h => by simp [ShardManifest.quadNativeConstantPredicates?] at h
  | .values _ _, _, h => by simp [ShardManifest.quadNativeConstantPredicates?] at h
  | .service _ _ _, _, h => by simp [ShardManifest.quadNativeConstantPredicates?] at h
  | .serviceVar _ _ _, _, h => by simp [ShardManifest.quadNativeConstantPredicates?] at h
  | .subSelect _, _, h => by simp [ShardManifest.quadNativeConstantPredicates?] at h
  | .empty, _, h => by simp [ShardManifest.quadNativeConstantPredicates?] at h

/-- The query-level form: what the planner's guard establishes. -/
theorem patternKept_of_queryPredicates (q : Query) (P : List WfIri)
    (h : ShardManifest.queryQuadConstantPredicates? q = some P) :
    PatternKept (keepPred P) q.pattern.rewriteBnodes := by
  simp only [ShardManifest.queryQuadConstantPredicates?] at h
  split at h
  · exact patternKept_of_quadPredicates _ P h
  · simp at h

#print axioms PatternKept_mono
#print axioms patternKept_of_quadPredicates
#print axioms patternKept_of_queryPredicates
#print axioms plannerSoundnessSelect
#print axioms plannerSoundnessAsk

end L4Factoidal.Storage.PlannerSoundness
