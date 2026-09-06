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

namespace L4Factoidal.Storage.PlannerSoundness

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.StoreDataset
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

#print axioms plannerSoundnessSelect
#print axioms plannerSoundnessAsk

end L4Factoidal.Storage.PlannerSoundness
