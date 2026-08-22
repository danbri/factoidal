/-
L4Factoidal.RDF.Graph — graphs, datasets, and graph operations.

Port of `formal/fstar/RDF.Graph.fsti` to Lean 4, plus the blank-node
renaming operation from `RDF.Dataset.Merge` that per-document
blank-node scoping needs.

An RDF graph is a SET of triples (RDF 1.1 Concepts §3). Like the F*
source, the representation is a `List Triple` so evaluation executes
directly, with set semantics maintained by the operations
(`Graph.mem` via the engine triple equality, `Graph.add`'s
deduplication) rather than by the representation type. A
`Finset`-based purely-specification twin is a candidate later layer;
this file is the executable one, matching the F* module it ports.
-/
import L4Factoidal.RDF.Core

namespace L4Factoidal.RDF

/-! ## Graphs — RDF 1.1 Concepts §3 ("a set of RDF triples") -/

/-- An RDF graph: a list of triples with set semantics maintained by
the operations below. -/
abbrev Graph := List Triple

def Graph.empty : Graph := []

/-- Membership via the engine triple equality `Triple.eqb` (literal
comparison goes through the language-tag / XMLLiteral rules, not raw
record equality) — port of `mem_triple`. -/
def Graph.mem (t : Triple) : Graph → Bool
  | []       => false
  | hd :: tl => hd.eqb t || Graph.mem t tl

/-- Set-based add: only add if not already present — port of
`graph_add`. -/
def Graph.add (t : Triple) (g : Graph) : Graph :=
  if g.mem t then g else g ++ [t]

/-- Graph union with deduplication: every triple of `g2` added to
`g1` set-wise. -/
def Graph.union (g1 g2 : Graph) : Graph :=
  g2.foldl (fun acc t => acc.add t) g1

/-! ## Blank-node renaming

RDF 1.1 Concepts §3.4: blank-node labels are document-scoped, so
merging graphs from separate documents must first rename each
document's labels apart (this is what makes graph MERGE different
from graph union). `renameBnodes f` applies a label mapping
everywhere a blank node can occur — including inside RDF 1.2 triple
terms. -/

def Subject.renameBnodes (f : BNodeId → BNodeId) : Subject → Subject
  | .iri i   => .iri i
  | .bnode b => .bnode (f b)

def Term.renameBnodes (f : BNodeId → BNodeId) : Term → Term
  | .iri i            => .iri i
  | .bnode b          => .bnode (f b)
  | .literal l        => .literal l
  | .tripleTerm s p o => .tripleTerm (s.renameBnodes f) p (o.renameBnodes f)

def Triple.renameBnodes (f : BNodeId → BNodeId) (t : Triple) : Triple :=
  { s := t.s.renameBnodes f, p := t.p, o := t.o.renameBnodes f }

def Graph.renameBnodes (f : BNodeId → BNodeId) (g : Graph) : Graph :=
  g.map (Triple.renameBnodes f)

/-- Prefix every blank-node label — the concrete renaming
`RDF.Dataset.Merge.rename_dataset_bnodes` uses to scope one parsed
document's labels apart from every other's. Injective for any prefix,
so distinct labels stay distinct. -/
def Graph.prefixBnodes (pre : String) (g : Graph) : Graph :=
  g.renameBnodes (fun b => pre ++ b)

/-! ## Datasets — RDF 1.1 Concepts §4 -/

/-- One named graph: an IRI naming a graph. -/
structure NamedGraph where
  name  : Iri
  graph : Graph
  deriving Repr

/-- An RDF dataset: exactly one default graph plus zero or more named
graphs — the unit SPARQL's `FROM`/`FROM NAMED`/`GRAPH` clauses
(SPARQL 1.1 §13.2) query against. -/
structure Dataset where
  default : Graph
  named   : List NamedGraph
  deriving Repr

def Dataset.empty : Dataset := { default := [], named := [] }

/-- Look up a named graph by IRI (port of `lookup_named_graph`). -/
def Dataset.lookupNamed (name : Iri) (ds : Dataset) : Option Graph :=
  match ds.named.find? (fun ng => ng.name == name) with
  | some ng => some ng.graph
  | none    => none

/-! ## Set-semantics theorems -/

/-- Membership distributes over append. -/
theorem Graph.mem_append (g1 g2 : Graph) (u : Triple) :
    Graph.mem u (g1 ++ g2) = (Graph.mem u g1 || Graph.mem u g2) := by
  induction g1 with
  | nil => simp [Graph.mem]
  | cons hd tl ih => simp [Graph.mem, ih, Bool.or_assoc]

/-- `add` never loses membership. -/
theorem Graph.mem_add_of_mem (g : Graph) (t u : Triple)
    (h : g.mem u = true) : (g.add t).mem u = true := by
  unfold Graph.add
  by_cases hm : g.mem t = true <;> simp [hm, Graph.mem_append, h]

/-- The added triple is a member of the result (via `Triple.eqb`
reflexivity). -/
theorem Graph.mem_add_self (g : Graph) (t : Triple) :
    (g.add t).mem t = true := by
  unfold Graph.add
  by_cases hm : g.mem t = true <;> simp [hm, Graph.mem_append, Graph.mem]

/-! ## List membership vs engine membership; `add` and length

Harvested 2026-08-22 from the rdfs-core closure proofs. -/

/-- List membership implies engine membership (`Triple.eqb` is
reflexive). -/
theorem graphMem_of_mem {g : Graph} {t : Triple} (h : t ∈ g) :
    Graph.mem t g = true := by
  induction g with
  | nil => cases h
  | cons hd tl ih =>
    rcases List.mem_cons.mp h with rfl | h'
    · simp [Graph.mem]
    · simp [Graph.mem, ih h']

/-- Engine membership is witnessed by an eqb-equal list element. -/
theorem exists_of_graphMem {g : Graph} {t : Triple}
    (h : Graph.mem t g = true) : ∃ u, u ∈ g ∧ Triple.eqb u t = true := by
  induction g with
  | nil => simp [Graph.mem] at h
  | cons hd tl ih =>
    simp only [Graph.mem, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨hd, List.mem_cons_self .., h⟩
    · obtain ⟨u, hu, he⟩ := ih h
      exact ⟨u, List.mem_cons_of_mem _ hu, he⟩

theorem mem_add_of_mem_list {g : Graph} {t u : Triple} (h : t ∈ g) :
    t ∈ g.add u := by
  unfold Graph.add
  split
  · exact h
  · exact List.mem_append_left _ h

theorem mem_add_cases {g : Graph} {t u : Triple} (h : t ∈ g.add u) :
    t ∈ g ∨ t = u := by
  unfold Graph.add at h
  split at h
  · exact Or.inl h
  · rcases List.mem_append.mp h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (List.mem_singleton.mp h')

theorem length_le_add (g : Graph) (u : Triple) :
    g.length ≤ (g.add u).length := by
  unfold Graph.add
  split
  · exact Nat.le_refl _
  · simp

theorem add_eq_of_length_eq {g : Graph} {u : Triple}
    (h : (g.add u).length = g.length) : g.add u = g := by
  by_cases hm : g.mem u = true
  · simp [Graph.add, hm]
  · simp [Graph.add, hm] at h

theorem graphMem_of_exists {g : Graph} {t : Triple}
    (h : ∃ u, u ∈ g ∧ Triple.eqb u t = true) : Graph.mem t g = true := by
  obtain ⟨u, hu, he⟩ := h
  induction g with
  | nil => cases hu
  | cons hd tl ih =>
    rcases List.mem_cons.mp hu with rfl | h'
    · simp [Graph.mem, he]
    · simp [Graph.mem, ih h']

/-- Engine membership is closed under the engine equality. -/
theorem graphMem_of_graphMem_eqb {g : Graph} {u t : Triple}
    (h : Graph.mem u g = true) (he : Triple.eqb u t = true) :
    Graph.mem t g = true := by
  obtain ⟨v, hv, hve⟩ := exists_of_graphMem h
  exact graphMem_of_exists ⟨v, hv, Triple.eqb_trans hve he⟩

end L4Factoidal.RDF
