/-
L4Factoidal.Unified.ClBridge — the CL/IKL → RDF translation against
the unified layer's own dataset embedding.

Item 3 of https://github.com/danbri/factoidal/issues/609. The tree
carries TWO renderings of "a proposition inside RDF":

1. `CL/ToRdf.lean` (https://github.com/danbri/factoidal/issues/580):
   a top-level CLIF sentence becomes a NAMED GRAPH whose name is the
   content address `urn:cl:that:sha256:<hex>` of its alpha-normalized
   canonical CLIF, holding the sentence record and the sentence's
   translatable atoms; the default graph carries decorations
   (`urn:cl:def:asserts`, link triples, `urn:cl:def:rdfProjection`).
   `CL/IklRegime.lean`'s `x-ikl-*` handler then merges the content of
   every ASSERTS-decorated proposition graph into the default graph at
   query time.
2. `Unified/DatasetEmbed.lean`: a named graph `(n, G)` becomes the
   single decoration `atom (name "urn:cl:def:names") [n, that (rdfBody
   G)]` under the dataset-wide existential closure, and asserts
   nothing about the world (`dataset_decoration_asserts_nothing`).

## The result: they DISAGREE, and the disagreement is machine-checked

`Unified/SparqlAdequacy.lean` states the regime's soundness against a
THIRD reading, `iklPremises ds` — the default graph's Skolem reading
plus EVERY named graph's. That reading asserts the content of every
named graph, asserted or merely mentioned. So:

* `premises_entail_content` — under `iklPremises`, the witness
  proposition's content triple is entailed;
* `embedding_refutes_content` — under `datasetToTheory`, the SAME
  content triple is NOT entailed, and stays unentailed under
  `PropAlphaInvariant` (issue 589's proposition-individuation
  minimum). The separating model is `typeBlindInterp`.

The witness is a real `ToRdf` output: `wDs` is the translation of the
CLIF text `((that (Dead OBL)))` — the guard `wDs_is_the_translation`
pins the byte-equality against the parser and the translator.

Two further facts about what `ikl_extend_entailed` proves:

* `mergeWhere_entailed` — the entailment holds for EVERY selection
  predicate over the named graphs, `CL.IklRegime.extendDataset`'s
  `urn:cl:def:asserts` test included and excluded. So the landed
  soundness theorem certifies nothing about the CHOICE of predicate:
  `mergeAll_entailed` is the same theorem for the regime that merges
  every named graph, believed propositions included — the narrowing
  issue 581 made (a link decoration does not assert) is invisible to
  it.
* `regime_sound_ikl` inherits exactly that: its premise reading is
  `iklPremises`, so it is soundness relative to a dataset reading in
  which assertion and mention are already identified.

## The repair, and what it costs

`IklAssertionCommitment` states the regime's own encoding commitment
(`CL/IklRegime.lean`, "Encoding commitment") as an interpretation
condition over the decoration vocabulary alone: if `x` stands in the
`urn:cl:def:names` relation to a proposition `q` and something asserts
`x` through `urn:cl:def:asserts`, then `q` holds. Under that condition
plus graph-body coherence, the dataset embedding DOES entail the
regime's extended default graph on the blank-node-free fragment
(`embed_entails_extension`), and the two renderings agree.

`commitment_not_derivable` shows the condition is not free: it fails
in `typeBlindInterp`, which satisfies everything else.

## Fragment guard

`embed_entails_extension` is stated for a dataset with NO blank nodes
(`datasetBnodeNames ds = []`). Every `ToRdf` output satisfies it —
`toRdfDataset` emits only IRIs, literals and triple terms — but that
is pinned here by `#guard` on the witness, not proved for all texts.
Outside that fragment the dataset closure binds blank names that the
Skolem reading leaves free, and the two readings differ for a second,
unrelated reason.

Nothing here says anything about the sentences `ToRdf` reports in
`skipped`: quantified sentences, `or`/`not`/`if`/`iff`, equations,
sequence markers, functional terms and nested `that` arguments are
outside the translatable fragment, contribute no atoms to the
proposition graph, and are carried only as the sentence-record
literal.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Unified.SparqlAdequacy
import L4Factoidal.Unified.Witnesses

namespace L4Factoidal.Unified

open L4Factoidal

/-! ## 1. The selection predicate is invisible to the soundness proof

`CL.IklRegime.extendDataset` folds the named graphs into the default
graph under one test. `mergeWhere` is that fold with the test as a
parameter. -/

/-- Merge into the default graph the content of every named graph the
predicate selects. `CL.IklRegime.extendDataset` is one instance. -/
def mergeWhere (P : RDF.NamedGraph → Bool) (ds : RDF.Dataset) : RDF.Dataset :=
  { ds with
    default := ds.named.foldl
      (fun acc ng => if P ng then RDF.Graph.union acc ng.graph else acc)
      ds.default }

/-- The regime handler is `mergeWhere` at its own predicate. -/
theorem extendDataset_eq_mergeWhere (r : CL.IklRegime) (ds : RDF.Dataset) :
    CL.IklRegime.extendDataset r ds =
      mergeWhere (fun ng => CL.isPropositionGraphName ng.name &&
                            CL.assertsDecorated ds.default ng.name) ds := rfl

/-- `mem_iklFold` with the predicate CARRIED: a triple of the merged
default graph either was there, or comes from a SELECTED named
graph. -/
theorem mem_mergeFold (P : RDF.NamedGraph → Bool) :
    ∀ (ns : List RDF.NamedGraph) (acc : RDF.Graph) {t : RDF.Triple},
      t ∈ ns.foldl (fun acc ng =>
            if P ng then RDF.Graph.union acc ng.graph else acc) acc →
        t ∈ acc ∨ ∃ ng ∈ ns, P ng = true ∧ t ∈ ng.graph
  | [], acc, t, h => Or.inl h
  | ng :: rest, acc, t, h => by
      simp only [List.foldl_cons] at h
      rcases mem_mergeFold P rest _ h with h | ⟨ng', hng', hp', ht'⟩
      · by_cases hp : P ng = true
        · rw [if_pos hp] at h
          rcases mem_graphUnion _ _ h with h | h
          · exact Or.inl h
          · exact Or.inr ⟨ng, List.mem_cons_self .., hp, h⟩
        · rw [if_neg hp] at h
          exact Or.inl h
      · exact Or.inr ⟨ng', List.mem_cons_of_mem _ hng', hp', ht'⟩

/-- **The soundness proof does not see the predicate**: for EVERY
selection predicate, the merged default graph's Skolem reading is
entailed by the dataset's own graphs. `ikl_extend_entailed` is the
instance at the regime's `urn:cl:def:asserts` test. -/
theorem mergeWhere_entailed (P : RDF.NamedGraph → Bool) (ds : RDF.Dataset) :
    Unified.Entails (iklPremises ds) (rdfToTheorySk (mergeWhere P ds).default) := by
  intro i _ hsat
  refine (satisfies_rdfToTheorySk_iff i _).mpr (fun t ht => ?_)
  have hd : CL.Satisfies i (rdfToTheorySk ds.default) :=
    hsat _ (List.mem_cons_self ..)
  rcases mem_mergeFold P ds.named ds.default ht with h | ⟨ng, hng, _, htg⟩
  · exact (satisfies_rdfToTheorySk_iff i ds.default).mp hd t h
  · have hg : CL.Satisfies i (rdfToTheorySk ng.graph) :=
      hsat _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨ng, hng, rfl⟩))
    exact (satisfies_rdfToTheorySk_iff i ng.graph).mp hg t htg

/-- The merge-EVERYTHING regime — the one issue 581's narrowing
removed, which flattens the content of merely believed propositions —
has the identical soundness theorem. -/
theorem mergeAll_entailed (ds : RDF.Dataset) :
    Unified.Entails (iklPremises ds)
      (rdfToTheorySk (mergeWhere (fun _ => true) ds).default) :=
  mergeWhere_entailed _ ds

/-! ## 2. The witness: a real `ToRdf` output

The CLIF text `((that (Dead OBL)))` — IKL's cancelling-parentheses
assertion of `(Dead OBL)`, clause 2 of `CL/ToRdf.lean`'s translation
rules. -/

/-- The `urn:cl:` base the regime's `propositionGraphPrefix`
recognises. -/
def wBase : CL.IriBase := ⟨"urn:cl:", rfl⟩

/-- The sentence `(Dead OBL)`. -/
def wSentence : CL.Sentence := .atom (.name "Dead") [.term (.name "OBL")]

/-- The proposition IRI: `<urn:cl:that:sha256:…>`, the content address
of `wSentence`'s alpha-normalized canonical CLIF. -/
def wProp : RDF.WfIri := CL.propIri wBase wSentence

/-- The proposition's content triple, `<urn:cl:OBL> rdf:type
<urn:cl:Dead>`. -/
def wContent : RDF.Triple :=
  { s := .iri (CL.nameIri wBase "OBL"), p := CL.rdfTypeIri,
    o := .iri (CL.nameIri wBase "Dead") }

/-- The default graph's assertion decoration. -/
def wAsserts : RDF.Triple :=
  { s := .iri CL.clKbIri, p := CL.clDefAssertsIri, o := .iri wProp }

/-- The default graph's rdf-projection decoration. -/
def wProjection : RDF.Triple :=
  { s := .iri wProp, p := CL.clDefRdfProjectionIri,
    o := .tripleTerm wContent.s wContent.p wContent.o }

/-- The dataset `CL.toRdfDataset` produces for the witness text. -/
def wDs : RDF.Dataset :=
  { default := [wAsserts, wProjection],
    named := [{ name := .iri wProp,
                graph := [CL.recordTriple wProp wSentence, wContent] }] }

/-- The witness text, parsed and translated by the real pipeline. -/
def wTranslated : Option RDF.Dataset :=
  match CL.parseClifText "((that (Dead OBL)))" with
  | .error _ => none
  | .ok ss =>
      match CL.toRdfDataset "urn:cl:" ss with
      | .error _ => none
      | .ok r => some r.ds

-- `wDs` IS the translation of the CLIF text — not a dataset shaped
-- like one.
#guard wTranslated == some wDs

-- The witness carries no blank nodes: the fragment guard of
-- `embed_entails_extension` holds for it.
#guard datasetBnodeNames wDs == ([] : List String)

-- The regime merges the proposition's content into the default graph.
#guard (CL.IklRegime.extendDataset ⟨"flat"⟩ wDs).default.mem wContent

/-! ## 3. The divergence -/

/-- Under the regime's premise reading the content is entailed. -/
theorem premises_entail_content :
    Unified.Entails (iklPremises wDs) (tripleAtom wContent) := by
  intro i _ hsat
  have hg : CL.Satisfies i (rdfToTheorySk
      [CL.recordTriple wProp wSentence, wContent]) :=
    hsat _ (by simp [iklPremises, wDs])
  exact (satisfies_rdfToTheorySk_iff i _).mp hg wContent (by simp)

/-- The separating model: every name denotes `true` except
`rdf:type`, and a predication holds exactly when its PREDICATE's
individual is `true`. It satisfies each of the three decoration
vocabularies (`urn:cl:def:asserts`, `urn:cl:def:rdfProjection`,
`urn:cl:def:names`) and refutes every `rdf:type` predication. -/
def typeBlindInterp : CL.Interp where
  dom := Bool
  domWit := true
  iName := fun n => !(n == CL.rdfTypeIri.val)
  iStr := fun _ => true
  rel := fun p _ => p = true
  fn := fun _ _ => true
  iProp := fun _ _ _ => true

/-- The proposition denotation is constant, so alpha-variants receive
one proposition: issue 589's individuation minimum holds. -/
theorem typeBlind_alphaInvariant : PropAlphaInvariant typeBlindInterp :=
  fun _ _ _ _ _ => rfl

theorem typeBlind_satisfies_wDs :
    CL.Satisfies typeBlindInterp (datasetToTheory wDs) := by
  refine (satisfies_datasetToTheory_iff _ _).mpr
    ⟨fun _ => true, fun t ht => ?_, fun ng hng => ?_⟩
  · have hnil : datasetBnodeNames wDs = [] := by decide
    rcases List.mem_cons.mp ht with rfl | ht
    · simp [tripleAtom, CL.Sat, CL.denotTerm, overrideOn, hnil,
            typeBlindInterp, wAsserts, CL.clDefAssertsIri, CL.rdfTypeIri]
    · obtain rfl := List.mem_singleton.mp ht
      simp [tripleAtom, CL.Sat, CL.denotTerm, overrideOn, hnil,
            typeBlindInterp, wProjection, CL.clDefRdfProjectionIri,
            CL.rdfTypeIri]
  · have hnil : datasetBnodeNames wDs = [] := by decide
    obtain rfl := List.mem_singleton.mp hng
    simp [namedGraphAtom, CL.Sat, CL.denotTerm, overrideOn, hnil,
          typeBlindInterp, namesOp, CL.rdfTypeIri]

/-- **The dataset embedding does not license the regime's merge**: the
content triple of an ASSERTS-decorated proposition graph is not
entailed by `datasetToTheory`, and stays unentailed under
`PropAlphaInvariant`. -/
theorem embedding_refutes_content :
    ¬ CL.EntailsUnder PropAlphaInvariant [datasetToTheory wDs]
        (tripleAtom wContent) := by
  intro h
  have hs := h typeBlindInterp typeBlind_alphaInvariant (fun s hs => by
    obtain rfl := List.mem_singleton.mp hs
    exact typeBlind_satisfies_wDs)
  simp [tripleAtom, CL.Satisfies, CL.Sat, CL.denotTerm,
        typeBlindInterp, wContent, CL.rdfTypeIri] at hs

/-- The same refutation over the whole interpretation class. -/
theorem embedding_refutes_content_plain :
    ¬ Unified.Entails [datasetToTheory wDs] (tripleAtom wContent) := by
  intro h
  exact embedding_refutes_content (fun i _ hsat => h i trivial hsat)

/-- **The two renderings disagree**, on one dataset that the CLIF
translator really produces: the regime's premise reading entails the
proposition's content, the unified layer's dataset embedding does
not. -/
theorem ikl_reading_diverges_from_dataset_embedding :
    Unified.Entails (iklPremises wDs) (tripleAtom wContent) ∧
    ¬ CL.EntailsUnder PropAlphaInvariant [datasetToTheory wDs]
        (tripleAtom wContent) :=
  ⟨premises_entail_content, embedding_refutes_content⟩

/-! ## 4. Non-vacuity of the divergence

A refutation over an interpretation class says nothing if the premise
is unsatisfiable or the conclusion is refuted by every model. Both
sides are checked. -/

/-- The premise of the refuted entailment is satisfiable — by the
separating model itself. -/
theorem divergence_premise_satisfiable :
    ∃ i : CL.Interp, PropAlphaInvariant i ∧
      CL.Satisfies i (datasetToTheory wDs) :=
  ⟨typeBlindInterp, typeBlind_alphaInvariant, typeBlind_satisfies_wDs⟩

/-- And the conclusion is not refuted by every model: the everywhere-
true interpretation satisfies it, so the entailment fails for the
right reason. -/
theorem divergence_conclusion_satisfiable :
    ∃ i : CL.Interp, PropAlphaInvariant i ∧
      CL.Satisfies i (tripleAtom wContent) :=
  ⟨trivialCLInterp, fun _ _ _ _ _ => rfl, by
    simp [tripleAtom, CL.Satisfies, CL.Sat, trivialCLInterp]⟩

/-! ## 5. Axiom audit -/

section Audits

#print axioms mergeWhere_entailed
#print axioms mergeAll_entailed
#print axioms extendDataset_eq_mergeWhere
#print axioms premises_entail_content
#print axioms typeBlind_satisfies_wDs
#print axioms embedding_refutes_content
#print axioms embedding_refutes_content_plain
#print axioms ikl_reading_diverges_from_dataset_embedding
#print axioms divergence_premise_satisfiable
#print axioms divergence_conclusion_satisfiable

end Audits

end L4Factoidal.Unified
