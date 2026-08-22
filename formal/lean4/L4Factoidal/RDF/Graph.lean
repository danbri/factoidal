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

end L4Factoidal.RDF
