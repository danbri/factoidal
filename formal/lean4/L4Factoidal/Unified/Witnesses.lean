/-
L4Factoidal.Unified.Witnesses — satisfiability and non-triviality
witnesses for the stage 1 theory layer
(https://github.com/danbri/factoidal/issues/598; design document
`docs/designissues/2026-08-25-unified-semantics-lean.md` §2.2), per
the discipline of `RDF/SemanticsHypothesisWitness.lean`: a theorem
whose hypothesis is unsatisfiable — or whose relation is the
everything-relation — verifies cleanly and says nothing.

What is checked, so that no stage 1 statement is vacuous:

* every translated graph and dataset is SATISFIABLE
  (`rdfToTheory_satisfiable`, `datasetToTheory_satisfiable`) — so
  `Entails [rdfToTheory g] ...` never holds by premise-vacuity;
* unified entailment between translations is NOT the
  everything-relation (`unified_entails_not_everything`) and not the
  empty relation on interesting pairs — a positive instance with a
  genuinely existential conclusion (`unified_entails_instance`);
* the `GraphTtFree` hypotheses of the decided corollary are
  satisfiable by a NON-EMPTY graph
  (`decided_hypotheses_inhabited`, reusing `RDF.witnessExact`);
* `PropAlphaInvariant` is satisfiable, by an interpretation whose
  proposition domain genuinely distinguishes sentences (keyed on
  `alphaNorm`), and entailment over that condition bundle is not the
  everything-relation;
* the NAMING decoration ASSERTS NOTHING: a model satisfies a
  named-graph-only dataset while refuting the named graph's content
  (`dataset_decoration_asserts_nothing`) — the design document
  §2.4's "asserts nothing about the world", machine-checked. After
  the https://github.com/danbri/factoidal/issues/609 item-3 repair
  this is the statement about a named graph the default graph does
  NOT decorate with `urn:cl:def:asserts`: `decorationDataset` has an
  empty default graph, so `graphAsserted` is false for it and the
  embedding contributes the naming decoration alone. An ASSERTED
  named graph is a different matter — its content IS entailed, under
  IKL coherence (`Unified/ClBridge.lean`,
  `embedding_entails_content`).

Anti-pattern #24 note for the gate theorems themselves:
`unified_adequate_simple` is an unconditional iff (no premise to
smuggle anything through); the decided corollary's only premises are
the two `GraphTtFree` facts, shown non-degenerately satisfiable here,
and its conclusion mentions neither.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Unified.RdfAdequacy
import L4Factoidal.Unified.DatasetEmbed
import L4Factoidal.RDF.SemanticsHypothesisWitness

namespace L4Factoidal.Unified

/-! ## Shared witness data -/

private def wA : RDF.WfIri := ⟨"http://w.example/a", by decide⟩
private def wP : RDF.WfIri := ⟨"http://w.example/p", by decide⟩
private def wG : RDF.WfIri := ⟨"http://w.example/g", by decide⟩

/-- A ground witness triple. -/
def wTriple : RDF.Triple := ⟨.iri wA, wP, .iri wA⟩

/-- A one-blank-node pattern the witness triple instantiates. -/
def wPattern : RDF.Triple := ⟨.bnode "y", wP, .iri wA⟩

theorem wTriple_ttFree : RDF.GraphTtFree [wTriple] := by
  intro t ht
  simp only [List.mem_singleton] at ht
  subst ht
  trivial

theorem wPattern_ttFree : RDF.GraphTtFree [wPattern] := by
  intro t ht
  simp only [List.mem_singleton] at ht
  subst ht
  trivial

theorem emptyGraph_ttFree : RDF.GraphTtFree ([] : RDF.Graph) := by
  intro t ht
  simp at ht

/-! ## 1. Translated graphs and datasets are satisfiable -/

/-- The everywhere-true interpretation. -/
def trivialCLInterp : CL.Interp where
  dom := Unit
  domWit := ()
  iName := fun _ => ()
  iStr := fun _ => ()
  rel := fun _ _ => True
  fn := fun _ _ => ()
  iProp := fun _ _ _ => ()

theorem rdfToTheory_satisfiable (g : RDF.Graph) :
    ∃ i : CL.Interp, CL.Satisfies i (rdfToTheory g) :=
  ⟨trivialCLInterp,
   (satisfies_rdfToTheory_restrict trivialCLInterp g).mpr
     ⟨fun _ => (), fun _ _ => True.intro⟩⟩

theorem datasetToTheory_satisfiable (ds : RDF.Dataset) :
    ∃ i : CL.Interp, CL.Satisfies i (datasetToTheory ds) := by
  refine ⟨trivialCLInterp,
    (satisfies_datasetToTheory_iff trivialCLInterp ds).mpr
      ⟨fun _ => (), fun t _ => ?_, fun ng _ => ?_, fun ng _ _ => ?_⟩⟩
  · simp [tripleAtom, CL.Sat, trivialCLInterp]
  · simp [namedGraphAtom, CL.Sat, trivialCLInterp]
  · simp [assertedGraphAtom, CL.Sat, trivialCLInterp]

/-! ## 2. The entailment relation is neither total nor empty -/

/-- Unified entailment between translations is not the
everything-relation: the empty graph does not entail a ground
triple. -/
theorem unified_entails_not_everything :
    ¬ Entails [rdfToTheory []] (rdfToTheory [wTriple]) := by
  intro hE
  have hDec := (unified_adequate_simple_decided [] [wTriple]
    emptyGraph_ttFree wTriple_ttFree).mp hE
  rw [show RDF.simpleEntails [] [wTriple] = false from by decide] at hDec
  exact Bool.false_ne_true hDec

/-- A positive instance with a genuinely existential conclusion: the
ground triple entails its blank-node pattern (the closure's
existential is witnessed, not vacuous). -/
theorem unified_entails_instance :
    Entails [rdfToTheory [wTriple]] (rdfToTheory [wPattern]) :=
  (unified_adequate_simple_decided [wTriple] [wPattern]
    wTriple_ttFree wPattern_ttFree).mpr (by decide)

/-! ## 3. The decided corollary's hypotheses are non-degenerate -/

theorem decided_hypotheses_inhabited :
    ∃ g : RDF.Graph, g ≠ [] ∧ RDF.GraphTtFree g :=
  ⟨RDF.witnessExact, RDF.witnessExact_nonempty, RDF.witnessExact_ttFree⟩

/-! ## 4. `PropAlphaInvariant` witnesses -/

/-- The syntactic proposition domain: sentences denote their own
alpha-normal forms, so alpha-variants collapse and nothing else
does. `relVal` parameterises the relation extension so the same
construction yields the satisfying and the refuting model. -/
def alphaKeyedInterp (relVal : Prop) : CL.Interp where
  dom := CL.Sentence
  domWit := .conj []
  iName := fun _ => .conj []
  iStr := fun _ => .conj []
  rel := fun _ _ => relVal
  fn := fun _ _ => .conj []
  iProp := fun s _ _ => s.alphaNorm

theorem alphaKeyed_invariant (relVal : Prop) :
    PropAlphaInvariant (alphaKeyedInterp relVal) :=
  fun _ _ _ _ h => h

/-- The bundle is satisfiable — `EntailsUnder PropAlphaInvariant` is
not vacuously the everything-relation. -/
theorem propAlphaInvariant_satisfiable :
    ∃ i : CL.Interp, PropAlphaInvariant i :=
  ⟨alphaKeyedInterp True, alphaKeyed_invariant True⟩

/-- And not the everything-relation for the other reason either: a
coherently alpha-invariant interpretation refutes a plain atom. -/
theorem propAlphaInvariant_entails_not_everything :
    ¬ CL.EntailsUnder PropAlphaInvariant []
        (.atom (.name "http://w.example/p") []) := by
  intro h
  have hs := h (alphaKeyedInterp False) (alphaKeyed_invariant False)
    (fun s hs => nomatch hs)
  simp [CL.Satisfies, CL.Sat, alphaKeyedInterp] at hs

/-- The proposition domain is not degenerate: two sentences that are
not alpha-variants receive DISTINCT propositions. -/
theorem alphaKeyed_distinguishes :
    (alphaKeyedInterp True).iProp
        (.atom (.name "http://w.example/a") []) (fun _ => .conj []) (fun _ => [])
      ≠ (alphaKeyedInterp True).iProp
        (.atom (.name "http://w.example/b") []) (fun _ => .conj []) (fun _ => []) := by
  intro h
  have hA : (CL.Sentence.atom (.name "http://w.example/a") []).alphaNorm
      = CL.Sentence.atom (.name "http://w.example/a") [] := rfl
  have hB : (CL.Sentence.atom (.name "http://w.example/b") []).alphaNorm
      = CL.Sentence.atom (.name "http://w.example/b") [] := rfl
  have h2 : (CL.Sentence.atom (.name "http://w.example/a") [])
      = (CL.Sentence.atom (.name "http://w.example/b") []) := by
    have h3 := h
    simp only [alphaKeyedInterp] at h3
    rw [hA, hB] at h3
    exact h3
  injection h2 with hp _
  injection hp with hn
  exact absurd hn (by decide)

/-! ## 5. The dataset decoration asserts nothing -/

/-- A dataset that is ONLY a decoration: empty default graph, one
named graph holding the witness triple. -/
def decorationDataset : RDF.Dataset :=
  { default := [], named := [{ name := .iri wG, graph := [wTriple] }] }

/-- The separating model: only the naming relation's individual has a
non-empty relation extension. It satisfies every decoration and
refutes every witness-vocabulary predication. -/
def namesOnlyInterp : CL.Interp where
  dom := Bool
  domWit := true
  iName := fun n => n == namesOp
  iStr := fun _ => false
  rel := fun p _ => p = true
  fn := fun _ _ => false
  iProp := fun _ _ _ => false

theorem namesOnly_satisfies_decoration :
    CL.Satisfies namesOnlyInterp (datasetToTheory decorationDataset) := by
  have hnil : datasetBnodeNames decorationDataset = [] := by decide
  refine (satisfies_datasetToTheory_iff _ _).mpr ⟨fun _ => false, ?_, ?_, ?_⟩
  · intro t ht
    exact absurd ht (by simp [decorationDataset])
  · intro ng hng
    simp only [decorationDataset, List.mem_singleton] at hng
    subst hng
    simp [namedGraphAtom, graphProp, CL.Sat, CL.denotTerm, overrideOn,
          namesOnlyInterp, hnil]
  · intro ng hng ha
    simp only [decorationDataset, List.mem_singleton] at hng
    subst hng
    exact absurd ha (by decide)

/-- **The decoration asserts nothing about the world** (design
document §2.4): a named-graph-only dataset does not entail its named
graph's content. -/
theorem dataset_decoration_asserts_nothing :
    ¬ Entails [datasetToTheory decorationDataset] (rdfToTheory [wTriple]) := by
  intro hE
  have hsat := hE namesOnlyInterp True.intro (fun s hs => by
    obtain rfl := List.mem_singleton.mp hs
    exact namesOnly_satisfies_decoration)
  rw [satisfies_rdfToTheory_iff] at hsat
  obtain ⟨f, hf⟩ := hsat
  have hgb : graphBnodeNames [wTriple] = ([] : List String) := by decide
  have hw := hf wTriple (by simp)
  rw [hgb] at hw
  simp [tripleAtom, CL.Sat, CL.denotTerm, overrideOn, namesOnlyInterp,
        wTriple, wP, namesOp] at hw

end L4Factoidal.Unified
