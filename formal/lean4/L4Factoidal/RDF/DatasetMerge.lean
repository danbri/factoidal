/-
L4Factoidal.RDF.DatasetMerge — per-document blank-node scoping.

Port of `formal/fstar/RDF.Dataset.Merge.fst` (69 lines).

RDF 1.1 scopes blank-node labels to the document they appear in. When a
consumer loads N documents into one dataset, each document's labels must
be made disjoint before merging. Label renaming is a semantic decision
about blank-node identity, so it lives here per iron rule #15, not in
consumer glue: consumers call `renameDatasetBnodes` with a distinct
prefix per input document (`"f0_"`, `"f1_"`, …) and then concatenate.

Renaming is a bijection on labels within one document — prefixing
preserves distinctness — so the renamed graph is isomorphic to the
input. No triple is gained, lost or merged within a document.

The F\* module exists because the Jena ARQ graph probe found the bug:
graph-09 and graph-10b joined `_:x` labels from separately loaded files
because the loader concatenated datasets without renaming.

## One difference from the F\*

`rename_graph_name` in F\* takes an `iri` — a plain string — and checks
for a `"_:"` prefix, because the F\* `named_graph`'s name slot is
IRI-typed and blank-node graph labels ride inside it as the literal
string `"_:<label>"` (the Parser.NQuads convention, also used by TriG
and JSON-LD). Lean's `NamedGraph.name` is `Subject`, which is
`iri | bnode`, so a blank-node graph name IS a blank node and the
the prefix goes straight on its label. The string-prefix test
and with it the possibility of a graph name that merely LOOKS like a
blank node being renamed.
-/
import L4Factoidal.RDF.Graph

namespace L4Factoidal.RDF

def renameBnodeLabel (pre : String) (b : BNodeId) : BNodeId := pre ++ b

def renameSubject (pre : String) : Subject → Subject
  | .bnode b => .bnode (renameBnodeLabel pre b)
  | s        => s

def renameTerm (pre : String) : Term → Term
  | .bnode b => .bnode (renameBnodeLabel pre b)
  | t        => t

def renameTriple (pre : String) (t : Triple) : Triple :=
  { s := renameSubject pre t.s, p := t.p, o := renameTerm pre t.o }

def renameGraphBnodes (pre : String) (g : Graph) : Graph :=
  g.map (renameTriple pre)

/-- A blank-node graph name is document-scoped exactly like a
    triple-level blank node, so it takes the same prefix: a blank node
    used both as a graph name and as a subject or object (JSON-LD
    toRdf/0117) keeps one identity after renaming, and equal labels from
    different documents stay disjoint. -/
def renameGraphName (pre : String) : Subject → Subject := renameSubject pre

def renameNamedGraph (pre : String) (ng : NamedGraph) : NamedGraph :=
  { name := renameGraphName pre ng.name,
    graph := renameGraphBnodes pre ng.graph }

def renameDatasetBnodes (pre : String) (ds : Dataset) : Dataset :=
  { default := renameGraphBnodes pre ds.default,
    named := ds.named.map (renameNamedGraph pre) }

/-! ## Build-time checks -/

private theorem exIri (s : String) : isIri ("http://e/" ++ s) = true := by
  simp [isIri, String.isEmpty]

private def mi (s : String) : WfIri := ⟨"http://e/" ++ s, exIri s⟩

private def docA : Graph :=
  [ ⟨.bnode "x", mi "p", .bnode "y"⟩,
    ⟨.iri (mi "a"), mi "p", .bnode "x"⟩ ]

private def docB : Graph :=
  [ ⟨.bnode "x", mi "q", .iri (mi "b")⟩ ]

/-! Renaming touches blank nodes and nothing else. -/

#guard renameGraphBnodes "f0_" docA ==
  [ ⟨.bnode "f0_x", mi "p", .bnode "f0_y"⟩,
    ⟨.iri (mi "a"), mi "p", .bnode "f0_x"⟩ ]

/-! The IRI subject and the predicate are untouched, which is what makes
    the renamed graph isomorphic to the input rather than merely
    similar. -/

#guard (renameGraphBnodes "f0_" docA).length == docA.length
#guard ((renameGraphBnodes "f0_" docA).filter (fun t => t.s == Subject.iri (mi "a"))).length == 1

/-! The bug this module exists for: `_:x` in two documents must NOT join
    after merging. Without renaming the two graphs share the label. -/

#guard (docA.filter (fun t => t.s == Subject.bnode "x")).length == 1
#guard (docB.filter (fun t => t.s == Subject.bnode "x")).length == 1
#guard ((renameGraphBnodes "f0_" docA ++ renameGraphBnodes "f1_" docB).filter
          (fun t => t.s == Subject.bnode "f0_x")).length == 1
#guard ((renameGraphBnodes "f0_" docA ++ renameGraphBnodes "f1_" docB).filter
          (fun t => t.s == Subject.bnode "x")).length == 0

/-! Within one document the SAME label stays one identity — `_:x` as a
    subject and `_:x` as an object are still the same node. That is what
    "bijection on labels" means, and a rename that freshened each
    occurrence would break it. -/

#guard ((renameGraphBnodes "f0_" docA).filter
          (fun t => t.o == Term.bnode "f0_x")).length == 1

/-! A blank-node GRAPH NAME takes the same prefix, so a blank node used
    both as a graph name and inside a triple keeps one identity. -/

private def dsm : Dataset :=
  { default := [], named := [{ name := .bnode "x", graph := docA }] }

#guard ((renameDatasetBnodes "f0_" dsm).named.map (·.name)) == [Subject.bnode "f0_x"]
#guard ((renameDatasetBnodes "f0_" dsm).named.map (·.graph.length)) == [docA.length]

/-! An IRI graph name is NOT renamed. -/

private def dsi : Dataset :=
  { default := [], named := [{ name := .iri (mi "g"), graph := [] }] }

#guard ((renameDatasetBnodes "f0_" dsi).named.map (·.name)) == [Subject.iri (mi "g")]

end L4Factoidal.RDF
