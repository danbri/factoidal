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

The divergence is not repaired by the IKL coherence condition either.
`embedding_refutes_content_ikl` refutes the same entailment over
`CL.IklRespectsThat`: coherence constrains a proposition's ZERO-ARY
relation extension, and the dataset embedding never puts the
`that`-term in that position — it sits in the second argument of
`urn:cl:def:names`.

## An IKL-coherent model, the first in this tree

That refutation needs a model of `CL.IklRespectsThat`, and none
existed anywhere in `formal/lean4` — so `CL.IklEntails` and
`CL.sat_assert_that` had no non-vacuity witness either. §5 builds one:
`propModel` has domain `Prop`, a proposition IS a `Prop`, and `pSat`
writes the model's own satisfaction out as a recursion, which breaks
the circularity between `CL.Sat` and `Interp.iProp`. `pSat_eq` proves
the recursion agrees with `CL.Sat` clause by clause.

## The repair, and what it costs

`IklAssertionCommitment` states the regime's own encoding commitment
(`CL/IklRegime.lean`, "Encoding commitment") as an interpretation
condition over the decoration vocabulary alone: if `x` stands in the
`urn:cl:def:names` relation to a proposition `q` and something asserts
`x` through `urn:cl:def:asserts`, then `q` holds. Under that condition
plus IKL coherence, the dataset embedding DOES entail the regime's
extended default graph on the blank-node-free fragment
(`embed_entails_extension`), and the two renderings agree.

`commitment_not_derivable` shows the condition is not free: it fails
in `coherentBlind`, which is IKL-coherent.
`embed_entails_extension_nonvacuous` shows the bundle has a model that
also satisfies the witness dataset's embedding, so the repair theorem
is not vacuous, and `commitModel_not_everything` shows that model is
not the everything-model.

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

/-- With no bound names, the override valuation is the interpretation's
own name mapping. -/
theorem overrideOn_nil {d : Type} (base f : String → d) :
    overrideOn base [] f = base := by
  funext n
  simp [overrideOn]

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

/-! ## 5. The IKL-coherent term model

Every statement above is over the whole interpretation class or over
`PropAlphaInvariant`. The condition the IKL guide actually imposes is
`CL.IklRespectsThat` — a proposition's zero-ary relation extension
agrees with satisfaction of the sentence expressing it. NO model of
that condition existed anywhere in this tree, so every theorem stated
over it (`CL.IklEntails` included) risked being vacuous.

The model below supplies one. Its domain is `Prop`; a sentence's
proposition IS a `Prop`, and `pSat` is the satisfaction function of
the model written out as a recursion, which is what breaks the
circularity — `CL.Sat` needs `iProp`, and `iProp` needs satisfaction.
`pSat_eq` proves the two agree, and `propModel_coherent` turns that
into coherence for every relation reading that makes zero-ary
predication transparent.

The construction is parameterised by the name, string, relation and
function readings, so the same recursion serves the refuting model of
§6 and the bundle-satisfiability model of §8. -/


mutual
def pDen (iS : String → Prop) (R F : Prop → List Prop → Prop)
    (ν : String → Prop) (σ : String → List Prop) : CL.Term → Prop
  | .name n => ν n
  | .str s => iS s
  | .funapp op args => F (pDen iS R F ν σ op) (pSeq iS R F ν σ args)
  | .that s => pSat iS R F ν σ s
termination_by t => sizeOf t

def pSeq (iS : String → Prop) (R F : Prop → List Prop → Prop)
    (ν : String → Prop) (σ : String → List Prop) : List CL.SeqItem → List Prop
  | [] => []
  | .term t :: r => pDen iS R F ν σ t :: pSeq iS R F ν σ r
  | .seqmark m :: r => σ m ++ pSeq iS R F ν σ r
termination_by xs => sizeOf xs

def pSat (iS : String → Prop) (R F : Prop → List Prop → Prop)
    (ν : String → Prop) (σ : String → List Prop) : CL.Sentence → Prop
  | .atom p args => R (pDen iS R F ν σ p) (pSeq iS R F ν σ args)
  | .eq a b => pDen iS R F ν σ a = pDen iS R F ν σ b
  | .conj ss => pAll iS R F ν σ ss
  | .disj ss => pAny iS R F ν σ ss
  | .neg s => ¬ pSat iS R F ν σ s
  | .impl a b => pSat iS R F ν σ a → pSat iS R F ν σ b
  | .iff a b => pSat iS R F ν σ a ↔ pSat iS R F ν σ b
  | .all bs body => pForall iS R F ν σ bs body
  | .ex bs body => pExists iS R F ν σ bs body
termination_by s => sizeOf s

def pAll (iS : String → Prop) (R F : Prop → List Prop → Prop)
    (ν : String → Prop) (σ : String → List Prop) : List CL.Sentence → Prop
  | [] => True
  | s :: r => pSat iS R F ν σ s ∧ pAll iS R F ν σ r
termination_by ss => sizeOf ss

def pAny (iS : String → Prop) (R F : Prop → List Prop → Prop)
    (ν : String → Prop) (σ : String → List Prop) : List CL.Sentence → Prop
  | [] => False
  | s :: r => pSat iS R F ν σ s ∨ pAny iS R F ν σ r
termination_by ss => sizeOf ss

def pForall (iS : String → Prop) (R F : Prop → List Prop → Prop)
    (ν : String → Prop) (σ : String → List Prop) :
    List CL.Binding → CL.Sentence → Prop
  | [], body => pSat iS R F ν σ body
  | .plain n :: r, body =>
      ∀ x : Prop, pForall iS R F (CL.updateInd ν n x) σ r body
  | .seqmark m :: r, body =>
      ∀ xs : List Prop, pForall iS R F ν (CL.updateSeq σ m xs) r body
  | .restricted n g :: r, body =>
      ∀ x : Prop, R (pDen iS R F ν σ g) [x] →
        pForall iS R F (CL.updateInd ν n x) σ r body
termination_by bs body => sizeOf bs + sizeOf body

def pExists (iS : String → Prop) (R F : Prop → List Prop → Prop)
    (ν : String → Prop) (σ : String → List Prop) :
    List CL.Binding → CL.Sentence → Prop
  | [], body => pSat iS R F ν σ body
  | .plain n :: r, body =>
      ∃ x : Prop, pExists iS R F (CL.updateInd ν n x) σ r body
  | .seqmark m :: r, body =>
      ∃ xs : List Prop, pExists iS R F ν (CL.updateSeq σ m xs) r body
  | .restricted n g :: r, body =>
      ∃ x : Prop, R (pDen iS R F ν σ g) [x] ∧
        pExists iS R F (CL.updateInd ν n x) σ r body
termination_by bs body => sizeOf bs + sizeOf body
end

/-- The Prop-domain term model. -/
@[reducible] def propModel (iN iS : String → Prop) (R F : Prop → List Prop → Prop) :
    CL.Interp where
  dom := Prop
  domWit := True
  iName := iN
  iStr := iS
  rel := R
  fn := F
  iProp := fun s ν σ => pSat iS R F ν σ s


theorem propModel_fn (iN iS : String → Prop) (R F : Prop → List Prop → Prop) :
    (propModel iN iS R F).fn = F := rfl
theorem propModel_rel (iN iS : String → Prop) (R F : Prop → List Prop → Prop) :
    (propModel iN iS R F).rel = R := rfl
theorem propModel_iStr (iN iS : String → Prop) (R F : Prop → List Prop → Prop) :
    (propModel iN iS R F).iStr = iS := rfl
theorem propModel_iName (iN iS : String → Prop) (R F : Prop → List Prop → Prop) :
    (propModel iN iS R F).iName = iN := rfl
theorem propModel_iProp (iN iS : String → Prop) (R F : Prop → List Prop → Prop) :
    (propModel iN iS R F).iProp = fun s ν σ => pSat iS R F ν σ s := rfl

mutual
theorem pDen_eq (iN iS : String → Prop) (R F : Prop → List Prop → Prop)
    (ν : String → Prop) (σ : String → List Prop) :
    ∀ t : CL.Term, CL.denotTerm (propModel iN iS R F) ν σ t = pDen iS R F ν σ t
  | .name _ => by simp only [CL.denotTerm, pDen] <;> rfl
  | .str _ => by simp only [CL.denotTerm, pDen, propModel_iStr] <;> rfl
  | .funapp op args => by
      simp only [CL.denotTerm, pDen, propModel_fn,
        pDen_eq iN iS R F ν σ op, pSeq_eq iN iS R F ν σ args] <;> rfl
  | .that _ => by simp only [CL.denotTerm, pDen, propModel_iProp] <;> rfl

theorem pSeq_eq (iN iS : String → Prop) (R F : Prop → List Prop → Prop)
    (ν : String → Prop) (σ : String → List Prop) :
    ∀ xs : List CL.SeqItem,
      CL.denotSeq (propModel iN iS R F) ν σ xs = pSeq iS R F ν σ xs
  | [] => by simp only [CL.denotSeq, pSeq] <;> rfl
  | .term t :: r => by
      simp only [CL.denotSeq, pSeq, pDen_eq iN iS R F ν σ t,
        pSeq_eq iN iS R F ν σ r] <;> rfl
  | .seqmark _ :: r => by
      simp only [CL.denotSeq, pSeq, pSeq_eq iN iS R F ν σ r] <;> rfl
end

mutual
theorem pSat_eq (iN iS : String → Prop) (R F : Prop → List Prop → Prop)
    (ν : String → Prop) (σ : String → List Prop) :
    ∀ s : CL.Sentence, CL.Sat (propModel iN iS R F) ν σ s = pSat iS R F ν σ s
  | .atom p args => by
      simp only [CL.Sat, pSat, propModel_rel, pDen_eq iN iS R F ν σ p,
        pSeq_eq iN iS R F ν σ args] <;> rfl
  | .eq a b => by
      simp only [CL.Sat, pSat, pDen_eq iN iS R F ν σ a,
        pDen_eq iN iS R F ν σ b] <;> rfl
  | .conj ss => by simp only [CL.Sat, pSat, pAll_eq iN iS R F ν σ ss] <;> rfl
  | .disj ss => by simp only [CL.Sat, pSat, pAny_eq iN iS R F ν σ ss] <;> rfl
  | .neg s => by simp only [CL.Sat, pSat, pSat_eq iN iS R F ν σ s] <;> rfl
  | .impl a b => by
      simp only [CL.Sat, pSat, pSat_eq iN iS R F ν σ a,
        pSat_eq iN iS R F ν σ b] <;> rfl
  | .iff a b => by
      simp only [CL.Sat, pSat, pSat_eq iN iS R F ν σ a,
        pSat_eq iN iS R F ν σ b] <;> rfl
  | .all bs body => by
      simp only [CL.Sat, pSat, pForall_eq iN iS R F ν σ bs body] <;> rfl
  | .ex bs body => by
      simp only [CL.Sat, pSat, pExists_eq iN iS R F ν σ bs body] <;> rfl

theorem pAll_eq (iN iS : String → Prop) (R F : Prop → List Prop → Prop)
    (ν : String → Prop) (σ : String → List Prop) :
    ∀ ss : List CL.Sentence,
      CL.SatAll (propModel iN iS R F) ν σ ss = pAll iS R F ν σ ss
  | [] => by simp only [CL.SatAll, pAll] <;> rfl
  | s :: r => by
      simp only [CL.SatAll, pAll, pSat_eq iN iS R F ν σ s,
        pAll_eq iN iS R F ν σ r] <;> rfl

theorem pAny_eq (iN iS : String → Prop) (R F : Prop → List Prop → Prop)
    (ν : String → Prop) (σ : String → List Prop) :
    ∀ ss : List CL.Sentence,
      CL.SatAny (propModel iN iS R F) ν σ ss = pAny iS R F ν σ ss
  | [] => by simp only [CL.SatAny, pAny] <;> rfl
  | s :: r => by
      simp only [CL.SatAny, pAny, pSat_eq iN iS R F ν σ s,
        pAny_eq iN iS R F ν σ r] <;> rfl

theorem pForall_eq (iN iS : String → Prop) (R F : Prop → List Prop → Prop)
    (ν : String → Prop) (σ : String → List Prop) :
    ∀ (bs : List CL.Binding) (body : CL.Sentence),
      CL.SatForall (propModel iN iS R F) ν σ bs body = pForall iS R F ν σ bs body
  | [], body => by
      simp only [CL.SatForall, pForall, pSat_eq iN iS R F ν σ body] <;> rfl
  | .plain n :: r, body => by
      simp only [CL.SatForall, pForall,
        fun x => pForall_eq iN iS R F (CL.updateInd ν n x) σ r body] <;> rfl
  | .seqmark m :: r, body => by
      simp only [CL.SatForall, pForall,
        fun xs => pForall_eq iN iS R F ν (CL.updateSeq σ m xs) r body] <;> rfl
  | .restricted n g :: r, body => by
      simp only [CL.SatForall, pForall, propModel_rel, pDen_eq iN iS R F ν σ g,
        fun x => pForall_eq iN iS R F (CL.updateInd ν n x) σ r body] <;> rfl

theorem pExists_eq (iN iS : String → Prop) (R F : Prop → List Prop → Prop)
    (ν : String → Prop) (σ : String → List Prop) :
    ∀ (bs : List CL.Binding) (body : CL.Sentence),
      CL.SatExists (propModel iN iS R F) ν σ bs body = pExists iS R F ν σ bs body
  | [], body => by
      simp only [CL.SatExists, pExists, pSat_eq iN iS R F ν σ body] <;> rfl
  | .plain n :: r, body => by
      simp only [CL.SatExists, pExists,
        fun x => pExists_eq iN iS R F (CL.updateInd ν n x) σ r body] <;> rfl
  | .seqmark m :: r, body => by
      simp only [CL.SatExists, pExists,
        fun xs => pExists_eq iN iS R F ν (CL.updateSeq σ m xs) r body] <;> rfl
  | .restricted n g :: r, body => by
      simp only [CL.SatExists, pExists, propModel_rel, pDen_eq iN iS R F ν σ g,
        fun x => pExists_eq iN iS R F (CL.updateInd ν n x) σ r body] <;> rfl
end

/-- The term model is IKL-coherent whenever the relation reading makes
zero-ary predication transparent. -/
theorem propModel_coherent (iN iS : String → Prop)
    (R F : Prop → List Prop → Prop) (hR : ∀ p : Prop, R p [] ↔ p) :
    CL.IklRespectsThat (propModel iN iS R F) := by
  intro s ν σ
  show R (pSat iS R F ν σ s) [] ↔ _
  rw [hR, pSat_eq iN iS R F ν σ s]

/-! ## 6. The divergence, under the IKL coherence condition itself

`typeBlindInterp` of §3 is not IKL-coherent. `coherentBlind` is the
same separating idea inside the term model: every name denotes `True`
except `rdf:type`, and a predication holds exactly when its PREDICATE's
individual holds. It satisfies the three decoration vocabularies,
refutes every `rdf:type` predication, and is IKL-coherent. -/

/-- Every name denotes truth except `rdf:type`. -/
def blindName (n : String) : Prop := n ≠ CL.rdfTypeIri.val

/-- A predication holds exactly when its predicate's individual holds.
Zero-ary predication is transparent, which is what
`propModel_coherent` asks for. -/
def predRel (x : Prop) (_ : List Prop) : Prop := x

/-- A functional term denotes its operator's individual. -/
def opFn (x : Prop) (_ : List Prop) : Prop := x

/-- The IKL-coherent separating model. -/
def coherentBlind : CL.Interp :=
  propModel blindName (fun _ => True) predRel opFn

theorem coherentBlind_respectsThat : CL.IklRespectsThat coherentBlind :=
  propModel_coherent _ _ _ _ (fun _ => Iff.rfl)

theorem coherentBlind_satisfies_wDs :
    CL.Satisfies coherentBlind (datasetToTheory wDs) := by
  have hnil : datasetBnodeNames wDs = [] := by decide
  refine (satisfies_datasetToTheory_iff _ _).mpr
    ⟨fun _ => True, fun t ht => ?_, fun ng hng => ?_⟩
  · rcases List.mem_cons.mp ht with rfl | ht
    · simp only [tripleAtom, CL.Sat, CL.denotTerm, hnil, overrideOn_nil,
        coherentBlind, propModel, predRel, blindName, wAsserts,
        CL.clDefAssertsIri, CL.rdfTypeIri]
      decide
    · obtain rfl := List.mem_singleton.mp ht
      simp only [tripleAtom, CL.Sat, CL.denotTerm, hnil, overrideOn_nil,
        coherentBlind, propModel, predRel, blindName, wProjection,
        CL.clDefRdfProjectionIri, CL.rdfTypeIri]
      decide
  · obtain rfl := List.mem_singleton.mp hng
    simp only [namedGraphAtom, CL.Sat, CL.denotTerm, hnil, overrideOn_nil,
      coherentBlind, propModel, predRel, blindName, namesOp, CL.rdfTypeIri]
    decide

/-- **The divergence survives IKL coherence**: `CL.IklRespectsThat`
does not tie the `urn:cl:def:asserts` decoration to the truth of the
proposition it decorates, so the dataset embedding still refutes the
content the regime merges. -/
theorem embedding_refutes_content_ikl :
    ¬ CL.EntailsUnder CL.IklRespectsThat [datasetToTheory wDs]
        (tripleAtom wContent) := by
  intro h
  have hs := h coherentBlind coherentBlind_respectsThat (fun s hs => by
    obtain rfl := List.mem_singleton.mp hs
    exact coherentBlind_satisfies_wDs)
  simp only [tripleAtom, CL.Satisfies, CL.Sat, CL.denotTerm, coherentBlind,
    propModel, predRel, blindName, wContent] at hs
  exact hs rfl

/-! ## 7. The repair: the regime's encoding commitment, stated

`CL/IklRegime.lean`'s "Encoding commitment" section says in prose what
the regime adds to RDF: the proposition IRI is read BOTH as the
proposition's identifier and as the name of the graph holding its
projection, so an `urn:cl:def:asserts` decoration on that IRI makes the
proposition true. Stated over the decoration vocabulary alone, with no
mention of graphs, satisfaction or the translation, that is: -/

/-- If `x` stands in the `urn:cl:def:names` relation to a proposition
`q`, and something asserts `x` through `urn:cl:def:asserts`, then `q`
holds. -/
def IklAssertionCommitment (i : CL.Interp) : Prop :=
  ∀ x q s : i.dom,
    i.rel (i.iName namesOp) [x, q] →
    i.rel (i.iName CL.clDefAssertsIri.val) [s, x] →
    i.rel q []

/-- **The two renderings agree under the commitment**: on the
blank-node-free fragment, the dataset embedding entails the whole
extended default graph the `x-ikl-*` handler computes — every suffix,
and every asserting subject. -/
theorem embed_entails_extension (r : CL.IklRegime) (ds : RDF.Dataset)
    (hbn : datasetBnodeNames ds = []) :
    CL.EntailsUnder (fun i => CL.IklRespectsThat i ∧ IklAssertionCommitment i)
      [datasetToTheory ds]
      (rdfToTheorySk (CL.IklRegime.extendDataset r ds).default) := by
  rintro i ⟨hcoh, hcom⟩ hsat
  obtain ⟨f, hdef, hnamed⟩ :=
    (satisfies_datasetToTheory_iff i ds).mp (hsat _ (List.mem_singleton.mpr rfl))
  rw [hbn, overrideOn_nil] at hdef hnamed
  refine (satisfies_rdfToTheorySk_iff i _).mpr (fun t ht => ?_)
  rw [extendDataset_eq_mergeWhere] at ht
  simp only [mergeWhere] at ht
  rcases mem_mergeFold _ ds.named ds.default ht with h | ⟨ng, hng, hp, htg⟩
  · exact hdef t h
  · simp only [Bool.and_eq_true] at hp
    obtain ⟨_, hass⟩ := hp
    cases hn : ng.name with
    | bnode b => rw [hn] at hass; exact absurd hass (by simp [CL.assertsDecorated])
    | iri n =>
        rw [hn] at hass
        simp only [CL.assertsDecorated, List.any_eq_true, Bool.and_eq_true,
          beq_iff_eq] at hass
        obtain ⟨u, hu, hup, huo⟩ := hass
        have hun := hdef u hu
        have hgn := hnamed ng hng
        simp only [namedGraphAtom, CL.Sat, CL.denotTerm, CL.denotSeq, hn,
          embedSubject] at hgn
        simp only [tripleAtom, CL.Sat, CL.denotTerm, CL.denotSeq, hup, huo,
          embedTerm] at hun
        have hq := hcom _ _ _ hgn hun
        have hbody : CL.Sat i i.iName (fun _ => []) (rdfBody ng.graph) :=
          (hcoh (rdfBody ng.graph) i.iName (fun _ => [])).mp hq
        exact (satisfies_rdfToTheorySk_iff i ng.graph).mp hbody t htg

/-! ## 8. The commitment does work, and the bundle has a model -/

/-- The commitment is not derivable from IKL coherence: `coherentBlind`
satisfies `CL.IklRespectsThat` and fails it. -/
theorem commitment_not_derivable :
    CL.IklRespectsThat coherentBlind ∧ ¬ IklAssertionCommitment coherentBlind := by
  refine ⟨coherentBlind_respectsThat, fun h => ?_⟩
  have := h True False True (by
      simp only [coherentBlind, propModel, predRel, blindName, namesOp]
      decide) (by
      simp only [coherentBlind, propModel, predRel, blindName,
        CL.clDefAssertsIri, CL.rdfTypeIri]
      decide)
  exact this

/-- The relation reading that makes a binary predication hold exactly
when its OBJECT's individual holds — an assertion of `x` then carries
`x`, which is what the commitment asks for. -/
def objRel : Prop → List Prop → Prop
  | x, [] => x
  | _, [_, b] => b
  | _, _ => True

/-- A model of the whole bundle. -/
def commitModel : CL.Interp :=
  propModel (fun _ => True) (fun _ => True) objRel opFn

theorem commitModel_respectsThat : CL.IklRespectsThat commitModel :=
  propModel_coherent _ _ _ _ (fun _ => Iff.rfl)

theorem commitModel_commitment : IklAssertionCommitment commitModel := by
  intro x q s hnames _
  simpa only [commitModel, propModel, objRel] using hnames

/-- **The bundle of `embed_entails_extension` is satisfiable, and its
premise with it**: `commitModel` meets both conditions AND satisfies
the witness dataset's embedding, so the theorem is not vacuous. -/
theorem embed_entails_extension_nonvacuous :
    CL.IklRespectsThat commitModel ∧ IklAssertionCommitment commitModel ∧
      CL.Satisfies commitModel (datasetToTheory wDs) := by
  refine ⟨commitModel_respectsThat, commitModel_commitment, ?_⟩
  have hnil : datasetBnodeNames wDs = [] := by decide
  refine (satisfies_datasetToTheory_iff _ _).mpr
    ⟨fun _ => True, fun t ht => ?_, fun ng hng => ?_⟩
  · rcases List.mem_cons.mp ht with rfl | ht
    · simp [tripleAtom, CL.Sat, CL.denotTerm, CL.denotSeq, hnil, overrideOn_nil,
        commitModel, propModel, objRel, wAsserts, embedSubject, embedTerm]
    · obtain rfl := List.mem_singleton.mp ht
      simp [tripleAtom, CL.Sat, CL.denotTerm, CL.denotSeq, hnil, overrideOn_nil,
        commitModel, propModel, objRel, opFn, wProjection, embedSubject,
        embedTerm]
  · obtain rfl := List.mem_singleton.mp hng
    simp [namedGraphAtom, CL.Sat, CL.denotTerm, CL.denotSeq, hnil,
      overrideOn_nil, commitModel, propModel, objRel, pSat, rdfBody, pAll,
      tripleAtom, pDen, pSeq, opFn, embedSubject, embedTerm, CL.recordTriple,
      wContent]

/-- And the bundle is not degenerate: `commitModel` refutes a
sentence, so it is not the everything-model. -/
theorem commitModel_not_everything :
    ¬ CL.Satisfies commitModel (.neg (.atom (.name "p") [])) := by
  simp [CL.Satisfies, CL.Sat, CL.denotTerm, CL.denotSeq, commitModel,
    propModel, objRel]

/-! ## 9. Axiom audit -/

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
#print axioms pSat_eq
#print axioms propModel_coherent
#print axioms coherentBlind_respectsThat
#print axioms coherentBlind_satisfies_wDs
#print axioms embedding_refutes_content_ikl
#print axioms embed_entails_extension
#print axioms commitment_not_derivable
#print axioms commitModel_respectsThat
#print axioms commitModel_commitment
#print axioms embed_entails_extension_nonvacuous
#print axioms commitModel_not_everything

end Audits

end L4Factoidal.Unified
