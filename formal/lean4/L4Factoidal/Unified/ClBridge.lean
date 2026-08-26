/-
L4Factoidal.Unified.ClBridge — the assertion decoration on RDF named
graphs, against the unified layer's own dataset embedding.

Item 3 of https://github.com/danbri/factoidal/issues/609.
`Unified/DatasetEmbed.lean` renders a named graph `(n, G)` as the
naming decoration `atom (name "urn:cl:def:names") [n, that (rdfBody
G)]`, plus — when the default graph decorates `n` with
`urn:cl:def:asserts` — the zero-ary assertion `atom (that (rdfBody
G)) []`.

## The reading used to disagree with itself. §3 and §6 are the record

Before the item-3 repair, a named graph contributed the naming
decoration ALONE, so the `that`-term appeared only in the second
argument of a binary predication. `CL.IklRespectsThat` constrains a
proposition's ZERO-ARY relation extension and cannot reach that
position, so a proposition could be named and asserted in the dataset
while the theory refuted its content. That reading survives as
`Unified/DatasetEmbed.lean`'s `decorationOnlyToTheory`, and the
divergence is stated about it here, where it is true:

* `premises_entail_content` — under `iklPremises`, the witness
  proposition's content triple is entailed;
* `decorationOnly_refutes_content` — under `decorationOnlyToTheory`,
  the SAME content triple is NOT entailed, and stays unentailed under
  `PropAlphaInvariant` (the proposition-individuation minimum,
  separating model `typeBlindInterp`) and under `CL.IklRespectsThat`
  itself (§6, separating model `coherentBlind`).

## Provenance of the witness (2026-08-26)

`wDs` used to be a real output of `CL/ToRdf.lean` — an IKL-to-RDF
projection whose proposition graph names were content-addressed.
That projection was Claude-invented, never asked for, and is deleted
(https://github.com/danbri/factoidal/issues/626). The witness is now
built here from plain IRIs. Nothing in this module ever depended on
the graph name being a digest: every statement below turns on the
`urn:cl:def:asserts` decoration alone, and the statements of §1 and §8
that used to carry the digest-prefix test are now stated at the
assertion decoration by itself, which is strictly more general.

## The repair (§7): the assertion conjunct, and what it made derivable

`datasetToTheory` renders an ASSERTS-decorated named graph with the
zero-ary conjunct `atom (that (rdfBody G)) []` — CLIF's own
cancelling-parentheses assertion `((that S))`. Under
`CL.IklRespectsThat` alone, `CL.sat_assert_that` turns that conjunct
into the graph's content: `embed_asserts_decorated_graphs`.

That derivation REPLACES an adopted condition. The pre-repair version
of this module carried `IklAssertionCommitment` — the encoding
commitment stated as an interpretation condition over the decoration
vocabulary — together with `commitment_not_derivable`, which showed it
did not follow from IKL coherence. Both are gone: the embedding now
puts the `that`-term where coherence bites, so the commitment is not
needed as a condition and its negation-of-derivability no longer holds
of anything this module states.

`decorationOnly_strictly_weaker` measures the change: `coherentBlind`
satisfies the superseded reading of the witness dataset and refutes
the repaired one.

## §8: soundness over the dataset embedding, and it sees the predicate

`embed_entails_asserted_merge` and `asserted_merge_sound` are stated
over `[datasetToTheory ds]` under `CL.IklRespectsThat`. Until the
repair the corresponding statements sat in
`Unified/SparqlAdequacy.lean` over `iklPremises`, a reading that
asserts EVERY named graph, and §1's `mergeWhere_entailed` proves that
older statement for EVERY selection predicate over the named graphs —
so it certified nothing about the choice of the `urn:cl:def:asserts`
test, and did not see that a link decoration does not assert. The new
statement does see it: `embedding_sees_the_assertion_decoration`
entails the content over `wDs` and refutes it over `wDsMentioned` —
the same dataset with the assertion decoration deleted — while
`iklPremises` entails it over both.

## An IKL-coherent model, the first in this tree

The refutations of §6 need a model of `CL.IklRespectsThat`, and none
existed anywhere in `formal/lean4` — so `CL.IklEntails` and
`CL.sat_assert_that` had no non-vacuity witness either. §5 builds one:
`propModel` has domain `Prop`, a proposition IS a `Prop`, and `pSat`
writes the model's own satisfaction out as a recursion, which breaks
the circularity between `CL.Sat` and `Interp.iProp`. `pSat_eq` proves
the recursion agrees with `CL.Sat` clause by clause. `objModel`, the
instance of §8, is the non-vacuity witness for the repaired
embedding: IKL-coherent, satisfies `datasetToTheory wDs`, and refutes
a sentence.

## Fragment guard

`embed_entails_asserted_merge` is stated for a dataset with NO blank
nodes (`datasetBnodeNames ds = []`), pinned here by `#guard` on the
witness. Outside that fragment the dataset closure binds blank names
that the Skolem reading leaves free, and the two readings differ for a
second, unrelated reason.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Unified.SparqlAdequacy
import L4Factoidal.Unified.Witnesses

namespace L4Factoidal.Unified

open L4Factoidal

/-! ## 0. Local vocabulary

`rdf:type` as an RDF predicate, for the witness of §2 and for the
name-blind separating models of §3 and §6. -/

/-- `rdf:type`. -/
def rdfTypeIri : RDF.WfIri :=
  ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#type", rfl⟩

/-! ## 1. The selection predicate is invisible to the SUPERSEDED
soundness statement

A merge of named-graph content into the default graph is a fold under
one test. `mergeWhere` is that fold with the test as a parameter. The
measurement below is why the soundness statements of §8 are stated
over `datasetToTheory`. -/

/-- Merge into the default graph the content of every named graph the
predicate selects. -/
def mergeWhere (P : RDF.NamedGraph → Bool) (ds : RDF.Dataset) : RDF.Dataset :=
  { ds with
    default := ds.named.foldl
      (fun acc ng => if P ng then RDF.Graph.union acc ng.graph else acc)
      ds.default }

/-- The merge at the ASSERTION decoration: the content of every named
graph the default graph decorates with `urn:cl:def:asserts`. -/
def mergeAsserted (ds : RDF.Dataset) : RDF.Dataset :=
  mergeWhere (fun ng => graphAsserted ds ng) ds

/-- The merge fold, read backwards with the predicate CARRIED: a
triple of the merged default graph either was there, or comes from a
SELECTED named graph. -/
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

/-- **The superseded soundness statement does not see the
predicate**: for EVERY selection predicate, the merged default
graph's Skolem reading is entailed by the dataset's own graphs read
`iklPremises`-wise. The `urn:cl:def:asserts` test is one instance
(`asserted_merge_premises_entailed`); so is merging everything. -/
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

/-- The merge-EVERYTHING selection — the one that flattens the content
of merely mentioned propositions — has the identical soundness
theorem. -/
theorem mergeAll_entailed (ds : RDF.Dataset) :
    Unified.Entails (iklPremises ds)
      (rdfToTheorySk (mergeWhere (fun _ => true) ds).default) :=
  mergeWhere_entailed _ ds

/-- The SUPERSEDED soundness statement itself, at the assertion
decoration: the statement `Unified/SparqlAdequacy.lean` carried before
the issue-609 item-3 repair. Kept as the record — `mergeAll_entailed`
is the same theorem for the selection that ignores the decoration. -/
theorem asserted_merge_premises_entailed (ds : RDF.Dataset) :
    Unified.Entails (iklPremises ds)
      (rdfToTheorySk (mergeAsserted ds).default) :=
  mergeWhere_entailed _ ds

/-! ## 2. The witness

One named graph holding a content triple, and two default-graph
decorations: an `urn:cl:def:asserts` assertion of that graph, and an
`ist` LINK triple that mentions it without asserting it. Built from
plain IRIs — see the module header's provenance note. -/

/-- The proposition's graph name. -/
def wProp : RDF.WfIri := ⟨"urn:cl:p1", by decide⟩

/-- The proposition's content triple, `<urn:cl:OBL> rdf:type
<urn:cl:Dead>`. -/
def wContent : RDF.Triple :=
  { s := .iri ⟨"urn:cl:OBL", by decide⟩, p := rdfTypeIri,
    o := .iri ⟨"urn:cl:Dead", by decide⟩ }

/-- The default graph's assertion decoration. -/
def wAsserts : RDF.Triple :=
  { s := .iri ⟨"urn:cl:kb", by decide⟩, p := assertsIri, o := .iri wProp }

/-- A LINK decoration: `<urn:cl:c> ist <p1>` mentions the proposition
without asserting it. -/
def wLink : RDF.Triple :=
  { s := .iri ⟨"urn:cl:c", by decide⟩, p := ⟨"urn:cl:ist", by decide⟩,
    o := .iri wProp }

/-- The proposition graph: named by the proposition IRI, holding the
content triple. -/
def wPropGraph : RDF.NamedGraph :=
  { name := .iri wProp, graph := [wContent] }

/-- The witness dataset. -/
def wDs : RDF.Dataset :=
  { default := [wAsserts, wLink], named := [wPropGraph] }

-- The witness carries no blank nodes: the fragment guard of
-- `embed_entails_asserted_merge` holds for it.
#guard datasetBnodeNames wDs == ([] : List String)

-- The assertion-decoration merge carries the content into the default
-- graph ...
#guard (mergeAsserted wDs).default.mem wContent

-- ... and the unified layer's dataset reading asserts that named graph.
#guard graphAsserted wDs wPropGraph

/-- The MENTION-ONLY witness: `wDs` with its assertion decoration
deleted. The proposition is still named by its graph and still linked;
nothing asserts it. -/
def wDsMentioned : RDF.Dataset := { wDs with default := [wLink] }

-- Nothing asserts the proposition, so neither the assertion-decoration
-- merge nor the dataset embedding carries its content over ...
#guard !(graphAsserted wDsMentioned wPropGraph)
#guard !((mergeAsserted wDsMentioned).default.mem wContent)

-- ... while the merge-EVERYTHING selection does carry it over. That
-- gap is what `embedding_sees_the_assertion_decoration` turns into a
-- refutation.
#guard (mergeWhere (fun _ => true) wDsMentioned).default.mem wContent

#guard datasetBnodeNames wDsMentioned == ([] : List String)

/-- With no bound names, the override valuation is the interpretation's
own name mapping. -/
theorem overrideOn_nil {d : Type} (base f : String → d) :
    overrideOn base [] f = base := by
  funext n
  simp [overrideOn]

/-! ## 3. The divergence, over the SUPERSEDED embedding

Everything in this section and in §6 is stated about
`decorationOnlyToTheory` — the reading `Unified/DatasetEmbed.lean`
carried before the issue-609 item-3 repair, in which a named graph
contributed its naming decoration and nothing else. The statements are
kept because they are the record of why the embedding changed; they
are FALSE of the repaired `datasetToTheory` (§7). -/

/-- Under the regime's premise reading the content is entailed. -/
theorem premises_entail_content :
    Unified.Entails (iklPremises wDs) (tripleAtom wContent) := by
  intro i _ hsat
  have hg : CL.Satisfies i (rdfToTheorySk wPropGraph.graph) :=
    hsat _ (by simp [iklPremises, wDs])
  exact (satisfies_rdfToTheorySk_iff i _).mp hg wContent (by simp [wPropGraph])

/-- The separating model: every name denotes `true` except
`rdf:type`, and a predication holds exactly when its PREDICATE's
individual is `true`. It satisfies both decoration vocabularies
(`urn:cl:def:asserts`, `urn:cl:def:names`) and the link triple, and
refutes every `rdf:type` predication. -/
def typeBlindInterp : CL.Interp where
  dom := Bool
  domWit := true
  iName := fun n => !(n == rdfTypeIri.val)
  iStr := fun _ => true
  rel := fun p _ => p = true
  fn := fun _ _ => true
  iProp := fun _ _ _ => true

/-- The proposition denotation is constant, so alpha-variants receive
one proposition: issue 589's individuation minimum holds. -/
theorem typeBlind_alphaInvariant : PropAlphaInvariant typeBlindInterp :=
  fun _ _ _ _ _ => rfl

theorem typeBlind_satisfies_decorationOnly :
    CL.Satisfies typeBlindInterp (decorationOnlyToTheory wDs) := by
  have hnil : datasetBnodeNames wDs = [] := by decide
  refine (satisfies_decorationOnlyToTheory_iff _ _).mpr
    ⟨fun _ => true, fun t ht => ?_, fun ng hng => ?_⟩
  · rcases List.mem_cons.mp ht with rfl | ht
    · simp [tripleAtom, CL.Sat, CL.denotTerm, overrideOn, hnil,
            typeBlindInterp, wAsserts, assertsIri, assertsOp,
            rdfTypeIri] <;> decide
    · obtain rfl := List.mem_singleton.mp ht
      simp [tripleAtom, CL.Sat, CL.denotTerm, overrideOn, hnil,
            typeBlindInterp, wLink, rdfTypeIri] <;> decide
  · obtain rfl := List.mem_singleton.mp hng
    simp [namedGraphAtom, graphProp, CL.Sat, CL.denotTerm, overrideOn, hnil,
          typeBlindInterp, namesOp, rdfTypeIri]

/-- **The superseded embedding does not license the regime's merge**:
the content triple of an ASSERTS-decorated proposition graph is not
entailed by `decorationOnlyToTheory`, and stays unentailed under
`PropAlphaInvariant`. -/
theorem decorationOnly_refutes_content :
    ¬ CL.EntailsUnder PropAlphaInvariant [decorationOnlyToTheory wDs]
        (tripleAtom wContent) := by
  intro h
  have hs := h typeBlindInterp typeBlind_alphaInvariant (fun s hs => by
    obtain rfl := List.mem_singleton.mp hs
    exact typeBlind_satisfies_decorationOnly)
  simp [tripleAtom, CL.Satisfies, CL.Sat, CL.denotTerm,
        typeBlindInterp, wContent, rdfTypeIri] at hs

/-- The same refutation over the whole interpretation class. -/
theorem decorationOnly_refutes_content_plain :
    ¬ Unified.Entails [decorationOnlyToTheory wDs] (tripleAtom wContent) := by
  intro h
  exact decorationOnly_refutes_content (fun i _ hsat => h i trivial hsat)

/-- **The two renderings disagreed**: the premise reading entails the
proposition's content, the superseded decoration-only embedding does
not. Repaired by `embedding_entails_content` (§7). -/
theorem ikl_reading_diverges_from_decoration_only_embedding :
    Unified.Entails (iklPremises wDs) (tripleAtom wContent) ∧
    ¬ CL.EntailsUnder PropAlphaInvariant [decorationOnlyToTheory wDs]
        (tripleAtom wContent) :=
  ⟨premises_entail_content, decorationOnly_refutes_content⟩

/-! ## 4. Non-vacuity of the divergence

A refutation over an interpretation class says nothing if the premise
is unsatisfiable or the conclusion is refuted by every model. Both
sides are checked. -/

/-- The premise of the refuted entailment is satisfiable — by the
separating model itself. -/
theorem divergence_premise_satisfiable :
    ∃ i : CL.Interp, PropAlphaInvariant i ∧
      CL.Satisfies i (decorationOnlyToTheory wDs) :=
  ⟨typeBlindInterp, typeBlind_alphaInvariant, typeBlind_satisfies_decorationOnly⟩

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
refutes every `rdf:type` predication, and is IKL-coherent.

This is the section that names the defect exactly: coherence
constrains a proposition's ZERO-ARY relation extension, and the
superseded embedding never put the `that`-term in that position — it
sat in the second argument of `urn:cl:def:names`, where `predRel`
reads the OPERATOR and the `that`-term is never consulted. -/

/-- Every name denotes truth except `rdf:type`. -/
def blindName (n : String) : Prop := n ≠ rdfTypeIri.val

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

theorem coherentBlind_satisfies_decorationOnly :
    CL.Satisfies coherentBlind (decorationOnlyToTheory wDs) := by
  have hnil : datasetBnodeNames wDs = [] := by decide
  refine (satisfies_decorationOnlyToTheory_iff _ _).mpr
    ⟨fun _ => True, fun t ht => ?_, fun ng hng => ?_⟩
  · rcases List.mem_cons.mp ht with rfl | ht
    · simp only [tripleAtom, CL.Sat, CL.denotTerm, hnil, overrideOn_nil,
        coherentBlind, propModel, predRel, blindName, wAsserts,
        assertsIri, rdfTypeIri]
      decide
    · obtain rfl := List.mem_singleton.mp ht
      simp only [tripleAtom, CL.Sat, CL.denotTerm, hnil, overrideOn_nil,
        coherentBlind, propModel, predRel, blindName, wLink]
      decide
  · obtain rfl := List.mem_singleton.mp hng
    simp only [namedGraphAtom, graphProp, CL.Sat, CL.denotTerm, hnil,
      overrideOn_nil, coherentBlind, propModel, predRel, blindName, namesOp,
      rdfTypeIri]
    decide

/-- **The divergence survived IKL coherence**: `CL.IklRespectsThat`
did not tie the `urn:cl:def:asserts` decoration to the truth of the
proposition it decorates, so the superseded embedding still refuted
the content the regime merges. -/
theorem decorationOnly_refutes_content_ikl :
    ¬ CL.EntailsUnder CL.IklRespectsThat [decorationOnlyToTheory wDs]
        (tripleAtom wContent) := by
  intro h
  have hs := h coherentBlind coherentBlind_respectsThat (fun s hs => by
    obtain rfl := List.mem_singleton.mp hs
    exact coherentBlind_satisfies_decorationOnly)
  simp only [tripleAtom, CL.Satisfies, CL.Sat, CL.denotTerm, coherentBlind,
    propModel, predRel, blindName, wContent] at hs
  exact hs rfl

/-! ## 7. The repair: the assertion conjunct, and what it derives

The encoding commitment: an `urn:cl:def:asserts` decoration on a graph
name makes the proposition the graph's body expresses true.

Before the item-3 repair that had to be ADOPTED as an interpretation
condition (`IklAssertionCommitment`, over the decoration vocabulary
alone), because nothing in the embedding forced it —
`commitment_not_derivable` exhibited an IKL-coherent model in which it
failed. Both are removed. The embedding now emits the decorated
graph's proposition ZERO-ARILY, and `CL.sat_assert_that` does the rest:
the commitment is a THEOREM about any interpretation that satisfies the
embedding. -/

/-- **The encoding commitment, DERIVED**: under IKL coherence
alone, an interpretation satisfying the dataset embedding satisfies the
content of every named graph the default graph decorates with
`urn:cl:def:asserts`. -/
theorem embed_asserts_decorated_graphs {i : CL.Interp}
    (hcoh : CL.IklRespectsThat i) {ds : RDF.Dataset}
    (hbn : datasetBnodeNames ds = [])
    (hsat : CL.Satisfies i (datasetToTheory ds))
    {ng : RDF.NamedGraph} (hng : ng ∈ ds.named)
    (hass : graphAsserted ds ng = true) :
    CL.Satisfies i (rdfToTheorySk ng.graph) := by
  obtain ⟨f, _, _, hasserted⟩ := (satisfies_datasetToTheory_iff i ds).mp hsat
  rw [hbn, overrideOn_nil] at hasserted
  exact (sat_assertedGraphAtom i hcoh _ _ ng).mp (hasserted ng hng hass)

/-- **The divergence is gone**: on the same witness dataset, the
repaired embedding entails the asserted proposition's content, under
IKL coherence. Compare `decorationOnly_refutes_content_ikl`, the same
statement about the superseded reading. -/
theorem wDs_asserts_propGraph :
    graphAsserted wDs wPropGraph = true := by
  simp [graphAsserted, wDs, wPropGraph, wAsserts]

theorem embedding_entails_content :
    CL.EntailsUnder CL.IklRespectsThat [datasetToTheory wDs]
      (tripleAtom wContent) := by
  intro i hcoh hsat
  have h := embed_asserts_decorated_graphs hcoh (by decide)
    (hsat _ (List.mem_singleton.mpr rfl))
    (List.mem_singleton.mpr rfl) wDs_asserts_propGraph
  exact (satisfies_rdfToTheorySk_iff i wPropGraph.graph).mp h wContent
    (by simp [wPropGraph])

/-- **The two renderings agree**, on the dataset the divergence was
stated about: the premise reading and the unified layer's dataset
embedding both entail the asserted proposition's content. -/
theorem ikl_reading_agrees_with_dataset_embedding :
    Unified.Entails (iklPremises wDs) (tripleAtom wContent) ∧
    CL.EntailsUnder CL.IklRespectsThat [datasetToTheory wDs]
      (tripleAtom wContent) :=
  ⟨premises_entail_content, embedding_entails_content⟩

/-- The repaired reading is a STRICT strengthening of the superseded
one: `coherentBlind` satisfies `decorationOnlyToTheory wDs` and refutes
`datasetToTheory wDs`. With `datasetToTheory_entails_decorationOnly`
(`Unified/DatasetEmbed.lean`) this pins the inclusion as proper. -/
theorem decorationOnly_strictly_weaker :
    CL.Satisfies coherentBlind (decorationOnlyToTheory wDs) ∧
    ¬ CL.Satisfies coherentBlind (datasetToTheory wDs) := by
  refine ⟨coherentBlind_satisfies_decorationOnly, fun h => ?_⟩
  have hc := embedding_entails_content coherentBlind coherentBlind_respectsThat
    (fun s hs => by obtain rfl := List.mem_singleton.mp hs; exact h)
  simp only [tripleAtom, CL.Satisfies, CL.Sat, CL.denotTerm, coherentBlind,
    propModel, predRel, blindName, wContent] at hc
  exact hc rfl

/-! ## 8. Soundness of the assertion-decoration merge over the dataset
embedding

The statements `Unified/SparqlAdequacy.lean` carried over
`iklPremises` before the repair, restated over the unified layer's own
dataset reading. -/

/-- **The dataset embedding licenses the assertion-decoration merge**:
on the blank-node-free fragment, `datasetToTheory ds` entails the whole
merged default graph — every asserting subject — under
`CL.IklRespectsThat` alone. -/
theorem embed_entails_asserted_merge (ds : RDF.Dataset)
    (hbn : datasetBnodeNames ds = []) :
    CL.EntailsUnder CL.IklRespectsThat [datasetToTheory ds]
      (rdfToTheorySk (mergeAsserted ds).default) := by
  intro i hcoh hsat
  have hds := hsat _ (List.mem_singleton.mpr rfl)
  obtain ⟨f, hdef, _, _⟩ := (satisfies_datasetToTheory_iff i ds).mp hds
  rw [hbn, overrideOn_nil] at hdef
  refine (satisfies_rdfToTheorySk_iff i _).mpr (fun t ht => ?_)
  simp only [mergeAsserted, mergeWhere] at ht
  rcases mem_mergeFold _ ds.named ds.default ht with h | ⟨ng, hng, hp, htg⟩
  · exact hdef t h
  · exact (satisfies_rdfToTheorySk_iff i ng.graph).mp
      (embed_asserts_decorated_graphs hcoh hbn hds hng hp) t htg

/-- **Soundness of the assertion-decoration merge**: an answer the
engine returns over the merged default graph is a unified answer from
the dataset's own embedding, over the IKL-coherent interpretations. -/
theorem asserted_merge_sound (ds : RDF.Dataset)
    (hbn : datasetBnodeNames ds = [])
    {b : SPARQL.Bgp} {mu : SPARQL.Binding}
    (h : mu ∈ SPARQL.evalBgp b (mergeAsserted ds).default) :
    Answers CL.IklRespectsThat termEqSchema [datasetToTheory ds]
      (sparqlBgpToQuery b) mu := by
  intro i hcoh hS hsat
  exact unified_adequate_bgp_engine h i trivial hS (fun s hs => by
    obtain rfl := List.mem_singleton.mp hs
    exact embed_entails_asserted_merge ds hbn i hcoh hsat)

/-! ### The new statement DOES see the selection predicate

§1's `mergeWhere_entailed` holds for every predicate, so the
superseded statement certified nothing about the choice of the
`urn:cl:def:asserts` test. The replacement is refutable at a different
predicate: on `wDsMentioned` — `wDs` with its assertion decoration
deleted — the merge-everything selection's merged default graph is NOT
entailed by the embedding. -/

theorem coherentBlind_satisfies_wDsMentioned :
    CL.Satisfies coherentBlind (datasetToTheory wDsMentioned) := by
  have hnil : datasetBnodeNames wDsMentioned = [] := by decide
  refine (satisfies_datasetToTheory_iff _ _).mpr
    ⟨fun _ => True, fun t ht => ?_, fun ng hng => ?_, fun ng hng ha => ?_⟩
  · obtain rfl := List.mem_singleton.mp ht
    simp only [tripleAtom, CL.Sat, CL.denotTerm, hnil, overrideOn_nil,
      coherentBlind, propModel, predRel, blindName, wLink]
    decide
  · obtain rfl := List.mem_singleton.mp hng
    simp only [namedGraphAtom, graphProp, CL.Sat, CL.denotTerm, hnil,
      overrideOn_nil, coherentBlind, propModel, predRel, blindName, namesOp,
      rdfTypeIri]
    decide
  · obtain rfl := List.mem_singleton.mp hng
    exact absurd ha (by decide)

/-- Over `iklPremises`, the mentioned proposition's content is
entailed exactly as the asserted one's is — the reading does not
distinguish them. -/
theorem premises_entail_mentioned_content :
    Unified.Entails (iklPremises wDsMentioned) (tripleAtom wContent) := by
  intro i _ hsat
  have hg : CL.Satisfies i (rdfToTheorySk wPropGraph.graph) :=
    hsat _ (by simp [iklPremises, wDsMentioned, wDs])
  exact (satisfies_rdfToTheorySk_iff i _).mp hg wContent (by simp [wPropGraph])

/-- **The embedding does distinguish them**: the content of a
proposition that is named and linked but NOT asserted is not
entailed. -/
theorem embedding_refutes_mentioned_content :
    ¬ CL.EntailsUnder CL.IklRespectsThat [datasetToTheory wDsMentioned]
        (tripleAtom wContent) := by
  intro h
  have hs := h coherentBlind coherentBlind_respectsThat (fun s hs => by
    obtain rfl := List.mem_singleton.mp hs
    exact coherentBlind_satisfies_wDsMentioned)
  simp only [tripleAtom, CL.Satisfies, CL.Sat, CL.denotTerm, coherentBlind,
    propModel, predRel, blindName, wContent] at hs
  exact hs rfl

/-- **The choice of the `urn:cl:def:asserts` test is now visible in
the statement.** `mergeWhere_entailed` proves the superseded
soundness statement for every predicate, so it could not see the
choice. Over `datasetToTheory` the same content is entailed when the
default graph asserts the graph (`embedding_entails_content`, on
`wDs`) and refuted when it does not (on `wDsMentioned`, which differs
from `wDs` by the deletion of the assertion decoration alone) — while
`iklPremises` entails it in both cases. The `#guard`s of §2 pin the
executable half: the assertion-decoration merge does not carry the
mentioned graph's content, the merge-everything predicate does. -/
theorem embedding_sees_the_assertion_decoration :
    CL.EntailsUnder CL.IklRespectsThat [datasetToTheory wDs]
      (tripleAtom wContent) ∧
    ¬ CL.EntailsUnder CL.IklRespectsThat [datasetToTheory wDsMentioned]
      (tripleAtom wContent) ∧
    Unified.Entails (iklPremises wDsMentioned) (tripleAtom wContent) :=
  ⟨embedding_entails_content, embedding_refutes_mentioned_content,
   premises_entail_mentioned_content⟩

/-! ### Non-vacuity of the repaired statements -/

/-- The relation reading that makes a binary predication hold exactly
when its OBJECT's individual holds. -/
def objRel : Prop → List Prop → Prop
  | x, [] => x
  | _, [_, b] => b
  | _, _ => True

/-- The non-vacuity model. -/
def objModel : CL.Interp :=
  propModel (fun _ => True) (fun _ => True) objRel opFn

theorem objModel_respectsThat : CL.IklRespectsThat objModel :=
  propModel_coherent _ _ _ _ (fun _ => Iff.rfl)

/-- **The premise of `embed_entails_asserted_merge` is satisfiable
together with its condition**: `objModel` is IKL-coherent AND satisfies
the witness dataset's embedding, so the theorem is not vacuous. -/
theorem embed_entails_asserted_merge_nonvacuous :
    CL.IklRespectsThat objModel ∧ CL.Satisfies objModel (datasetToTheory wDs) := by
  refine ⟨objModel_respectsThat, ?_⟩
  have hnil : datasetBnodeNames wDs = [] := by decide
  refine (satisfies_datasetToTheory_iff _ _).mpr
    ⟨fun _ => True, fun t ht => ?_, fun ng hng => ?_, fun ng hng _ => ?_⟩
  · rcases List.mem_cons.mp ht with rfl | ht
    · simp [tripleAtom, CL.Sat, CL.denotTerm, CL.denotSeq, hnil, overrideOn_nil,
        objModel, propModel, objRel, wAsserts, embedSubject, embedTerm]
    · obtain rfl := List.mem_singleton.mp ht
      simp [tripleAtom, CL.Sat, CL.denotTerm, CL.denotSeq, hnil, overrideOn_nil,
        objModel, propModel, objRel, opFn, wLink, embedSubject,
        embedTerm]
  · obtain rfl := List.mem_singleton.mp hng
    simp [namedGraphAtom, graphProp, CL.Sat, CL.denotTerm, CL.denotSeq, hnil,
      overrideOn_nil, objModel, propModel, objRel, pSat, rdfBody, pAll,
      tripleAtom, pDen, pSeq, embedSubject, embedTerm,
      wContent, wPropGraph]
  · obtain rfl := List.mem_singleton.mp hng
    simp [assertedGraphAtom, graphProp, CL.Sat, CL.denotTerm, CL.denotSeq,
      hnil, overrideOn_nil, objModel, propModel, objRel, pSat, rdfBody, pAll,
      tripleAtom, pDen, pSeq, embedSubject, embedTerm,
      wContent, wPropGraph]

/-- And the model is not degenerate: `objModel` refutes a sentence, so
it is not the everything-model. -/
theorem objModel_not_everything :
    ¬ CL.Satisfies objModel (.neg (.atom (.name "p") [])) := by
  simp [CL.Satisfies, CL.Sat, CL.denotTerm, CL.denotSeq, objModel,
    propModel, objRel]

/-! ## 9. Axiom audit -/

section Audits

#print axioms mergeWhere_entailed
#print axioms mergeAll_entailed
#print axioms asserted_merge_premises_entailed
#print axioms premises_entail_content
#print axioms typeBlind_satisfies_decorationOnly
#print axioms decorationOnly_refutes_content
#print axioms decorationOnly_refutes_content_plain
#print axioms ikl_reading_diverges_from_decoration_only_embedding
#print axioms divergence_premise_satisfiable
#print axioms divergence_conclusion_satisfiable
#print axioms pSat_eq
#print axioms propModel_coherent
#print axioms coherentBlind_respectsThat
#print axioms coherentBlind_satisfies_decorationOnly
#print axioms decorationOnly_refutes_content_ikl
#print axioms embed_asserts_decorated_graphs
#print axioms embedding_entails_content
#print axioms ikl_reading_agrees_with_dataset_embedding
#print axioms decorationOnly_strictly_weaker
#print axioms embed_entails_asserted_merge
#print axioms asserted_merge_sound
#print axioms wDs_asserts_propGraph
#print axioms coherentBlind_satisfies_wDsMentioned
#print axioms premises_entail_mentioned_content
#print axioms embedding_refutes_mentioned_content
#print axioms embedding_sees_the_assertion_decoration
#print axioms objModel_respectsThat
#print axioms embed_entails_asserted_merge_nonvacuous
#print axioms objModel_not_everything

end Audits

end L4Factoidal.Unified
