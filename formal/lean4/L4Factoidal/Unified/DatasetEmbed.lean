/-
L4Factoidal.Unified.DatasetEmbed — RDF datasets in the unified theory
(https://github.com/danbri/factoidal/issues/598; design document
`docs/designissues/2026-08-25-unified-semantics-lean.md` §2.4).

* The DEFAULT graph is asserted: its triple atoms are conjuncts of the
  dataset sentence (`datasetToTheory_asserts_default`).
* Each NAMED graph `(n, G)` contributes ONE decoration sentence and
  asserts nothing about the world:
  `atom (name "urn:cl:def:names") [n, that (body of G)]` — the graph
  name stands in the naming relation to the proposition the graph's
  translation expresses. RDF 1.1 Concepts §4 deliberately gives
  datasets no entailment semantics; the decoration reading adds none
  (the witness `dataset_decoration_asserts_nothing` in
  `Unified/Witnesses.lean` checks that it adds none).
* Blank-node scope is DATASET-WIDE (RDF 1.1 Concepts §4: blank nodes
  may be shared between the graphs of one dataset): `datasetToTheory`
  closes existentially ONCE over every blank node of the dataset —
  the default graph's, each named graph's, and blank-node graph
  names — with the per-graph `that`-terms inside the closure. The
  proposition a shared-blank-node graph expresses then depends on the
  ambient valuation, which is exactly why `CL.Interp.iProp` takes the
  valuations as arguments (quantifying-in).

  CORRECTION to the design document §2.4: its decoration formula
  reads `that (rdfToTheory G)` — the CLOSED translation — while its
  own scoping bullet requires the dataset-wide closure with the
  that-terms inside it. Both cannot hold: re-closing `G` inside
  `that` would shadow the dataset-wide binding and lose exactly the
  sharing the bullet establishes. The decoration here carries
  `that (rdfBody G)` — the unscoped body — under the dataset-level
  closure, which is the reading the scoping bullet describes.

* `PropAlphaInvariant` — proposition identity is at least
  alpha-invariance (issue 589's semantic minimum, condition (1)):
  alpha-variant sentences express the same proposition. A CONDITION
  on interpretations, not a structural fact; its satisfiability and
  non-triviality witnesses are in `Unified/Witnesses.lean`. The
  stronger `=p` identities stay in the defined relation per
  issue 589 and are out of scope here.

The design document's DatasetEmbed row also names "N-Quads round-trip
corollaries". Not landed in stage 1: the tree's N-Quads/N-Triples
round-trip theorem exists only for the empty graph
(`Syntax/SyntaxTheorems.lean`, `graph_roundtrip_nil`; the general
statement is a commented-out skeleton there), so there is no native
theorem to compose with yet. The corollary lands when
https://github.com/danbri/factoidal/issues/576 does.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Unified.RdfTransport
import L4Factoidal.CL.Alpha

namespace L4Factoidal.Unified

/-! ## The dataset translation -/

/-- Every blank-node label of the dataset, dataset-wide: the default
graph's, then per named graph the graph-name label (a blank node may
name a graph — `NamedGraph.name : Subject`) and the graph's own. -/
def datasetBnodeIds (ds : RDF.Dataset) : List RDF.BNodeId :=
  RDF.graphBnodeIds ds.default
    ++ ds.named.flatMap
        (fun ng => RDF.subjectBnodes ng.name ++ RDF.graphBnodeIds ng.graph)

def datasetBnodeNames (ds : RDF.Dataset) : List String :=
  (datasetBnodeIds ds).map bnodeName

theorem datasetBnodeNames_no_colon (ds : RDF.Dataset) :
    ∀ n ∈ datasetBnodeNames ds, ':' ∉ n.toList := by
  intro n hn
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hn
  exact bnodeName_no_colon b

/-- One named graph's decoration: the graph name stands in the
`urn:cl:def:names` relation to the proposition the graph's (unscoped)
body expresses. -/
def namedGraphAtom (ng : RDF.NamedGraph) : CL.Sentence :=
  .atom (.name namesOp)
    [.term (embedSubject ng.name), .term (.that (rdfBody ng.graph))]

/-- The dataset body: the asserted default-graph atoms plus one
decoration per named graph. -/
def datasetBody (ds : RDF.Dataset) : CL.Sentence :=
  .conj (ds.default.map tripleAtom ++ ds.named.map namedGraphAtom)

/-- **The dataset translation** (design document §2.4): ONE sentence,
the dataset-wide existential closure of the dataset body. -/
def datasetToTheory (ds : RDF.Dataset) : CL.Sentence :=
  .ex ((datasetBnodeNames ds).map .plain) (datasetBody ds)

/-! ## Proposition individuation (issue 589, condition (1)) -/

/-- Alpha-variant sentences express the same proposition, at every
valuation. -/
def PropAlphaInvariant (i : CL.Interp) : Prop :=
  ∀ (s1 s2 : CL.Sentence) (ν : String → i.dom) (σ : String → List i.dom),
    s1.alphaNorm = s2.alphaNorm → i.iProp s1 ν σ = i.iProp s2 ν σ

/-! ## Satisfaction shape -/

theorem sat_datasetBody (i : CL.Interp) (ν : String → i.dom)
    (σ : String → List i.dom) (ds : RDF.Dataset) :
    CL.Sat i ν σ (datasetBody ds) ↔
      (∀ t ∈ ds.default, CL.Sat i ν σ (tripleAtom t)) ∧
      (∀ ng ∈ ds.named, CL.Sat i ν σ (namedGraphAtom ng)) := by
  unfold datasetBody
  simp only [CL.Sat]
  rw [satAll_forall]
  constructor
  · intro hh
    exact ⟨fun t ht => hh _ (List.mem_append_left _
             (List.mem_map.mpr ⟨t, ht, rfl⟩)),
           fun ng hng => hh _ (List.mem_append_right _
             (List.mem_map.mpr ⟨ng, hng, rfl⟩))⟩
  · rintro ⟨h1, h2⟩ s hs
    rcases List.mem_append.mp hs with hs | hs
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
      exact h1 t ht
    · obtain ⟨ng, hng, rfl⟩ := List.mem_map.mp hs
      exact h2 ng hng

/-- Satisfaction of a translated dataset, characterised: some
valuation of the dataset-wide bound names satisfies every asserted
atom and every decoration. -/
theorem satisfies_datasetToTheory_iff (i : CL.Interp) (ds : RDF.Dataset) :
    CL.Satisfies i (datasetToTheory ds) ↔
      ∃ f : String → i.dom,
        (∀ t ∈ ds.default,
          CL.Sat i (overrideOn i.iName (datasetBnodeNames ds) f)
            (fun _ => []) (tripleAtom t)) ∧
        (∀ ng ∈ ds.named,
          CL.Sat i (overrideOn i.iName (datasetBnodeNames ds) f)
            (fun _ => []) (namedGraphAtom ng)) := by
  unfold CL.Satisfies datasetToTheory
  simp only [CL.Sat]
  rw [satExists_plains]
  simp only [sat_datasetBody]

/-! ## What the translation asserts -/

/-- A dataset with no named graphs translates to exactly its default
graph's translation. -/
theorem datasetToTheory_no_named (g : RDF.Graph) :
    datasetToTheory { default := g, named := [] } = rdfToTheory g := by
  unfold datasetToTheory rdfToTheory datasetBody rdfBody
    datasetBnodeNames datasetBnodeIds graphBnodeNames
  simp

/-- **The default graph is asserted** (design document §2.4): the
dataset sentence entails the default graph's translation. -/
theorem datasetToTheory_asserts_default (ds : RDF.Dataset) :
    Entails [datasetToTheory ds] (rdfToTheory ds.default) := by
  intro i _ hsat
  obtain ⟨f, hdef, _⟩ := (satisfies_datasetToTheory_iff i ds).mp
    (hsat _ (List.mem_singleton.mpr rfl))
  have hν : FreshVal i (overrideOn i.iName (datasetBnodeNames ds) f) :=
    freshVal_overrideOn i (datasetBnodeNames_no_colon ds) f
  refine (satisfies_rdfToTheory_restrict i ds.default).mpr
    ⟨fun b => overrideOn i.iName (datasetBnodeNames ds) f (bnodeName b),
     fun t ht => ?_⟩
  exact (sat_tripleAtom_restrict i _ hν t (fun b _ => rfl)).mp (hdef t ht)

end L4Factoidal.Unified
