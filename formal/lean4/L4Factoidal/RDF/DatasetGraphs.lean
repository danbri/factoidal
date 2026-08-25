/-
L4Factoidal.RDF.DatasetGraphs — the graphs-first accessor surface.

Port of `formal/fstar/RDF.Dataset.Graphs.fst` (27 lines).

Every definition is a total composition of existing `RDF.Graph`
accessors, so the module carries no proof obligation beyond what
`Dataset` already does. RDF 1.1 assigns no semantics to the relation
between named graphs (the Zimmermann note), so this is vocabulary and
convention over `Dataset`, not a change to it.

## One difference from the F\*

`graph_ref` is `iri` in F\*, with a comment saying the type also carries
the `_:<label>` blank-node graph-name convention that
`RDF.Dataset.Merge.rename_graph_name` produces. Lean's `NamedGraph.name`
is already `Subject`, which is `iri | bnode` — so the convention is in
the TYPE here rather than in a comment on a string. `GraphRef` is
`Subject`.
-/
import L4Factoidal.RDF.Graph

namespace L4Factoidal.RDF

/-- A graph name. An IRI or a blank node — see the module header on why
    this is `Subject` and not `WfIri`. -/
abbrev GraphRef := Subject

/-- Every `(name, graph)` pair, the default graph excluded — SPARQL's
    `FROM NAMED` universe. Order matches `ds.named`. -/
def Dataset.graphs (ds : Dataset) : List (GraphRef × Graph) :=
  ds.named.map (fun ng => (ng.name, ng.graph))

/-- `lookupNamed` under the graphs-API name. -/
def Dataset.componentOf (ds : Dataset) (name : GraphRef) : Option Graph :=
  ds.lookupNamed name

/-! ## Build-time checks -/

private theorem exIri (s : String) : isIri ("http://e/" ++ s) = true := by
  simp [isIri, String.isEmpty]

private def gi (s : String) : GraphRef := .iri ⟨"http://e/" ++ s, exIri s⟩

private def dsx : Dataset :=
  { default := [], named := [{ name := gi "g1", graph := [] },
                             { name := .bnode "b1", graph := [] }] }

#guard (dsx.graphs.map (·.1)) == [gi "g1", Subject.bnode "b1"]
#guard (dsx.componentOf (gi "g1")).isSome
#guard (dsx.componentOf (.bnode "b1")).isSome
#guard (dsx.componentOf (gi "absent")).isNone

/-! The default graph is NOT in `graphs`, which is the whole point of
    the `FROM NAMED` universe. -/

#guard (Dataset.graphs { default := [], named := [] }).length == 0
#guard dsx.graphs.length == 2

end L4Factoidal.RDF
