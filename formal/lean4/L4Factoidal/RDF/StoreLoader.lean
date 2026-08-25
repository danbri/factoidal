/-
L4Factoidal.RDF.StoreLoader — the pure dataset folds behind the loaders.

Port of `formal/fstar/RDF.Store.Loader.fst` (118 lines).

The OCaml loaders own the I/O — opening a `.cottas` file, reading
parquet metadata, decoding columns, and the `try … with` around it.
What lives here is the PURE part that used to be inlined beside that
exception handling: merging several loaded datasets into one, and
bucketing a list of resolved quads into a default graph plus named
graphs.

## Bag semantics, deliberately

`mergePair` CONCATENATES. Duplicates are preserved, because these folds
combine sources and deduplication is a separate decision the caller
makes. That is the F\* module's semantics and it differs from
`Graph.add`, which is set-based — a `#guard` below pins the difference
so the two are not confused.

## One widening: a graph name is a Subject, not a String

The F\* `resolved_quad` carries `rq_graph : option string`, an IRI. The
Lean dataset model already carries `NamedGraph.name : Subject`, which
admits a blank node as a graph name — what RDF 1.1 §4 actually allows.
The port takes the wider type rather than narrowing the tree's own
model to match the F\* record.

## Order

Both folds accumulate in reverse and restore source order at the end:
`bucketQuads` reverses the default graph once and each named graph's
triples once. A `#guard` pins that the output is in source order, since
an accumulator fold that forgot a reverse would still typecheck and
still produce the right SET of triples.
-/
import L4Factoidal.RDF.Graph

namespace L4Factoidal.RDF

/-- Concatenate two datasets. Default graphs concatenate; named-graph
    LISTS concatenate, so two entries for the same name stay separate
    at this level — `bucketQuads` is where grouping by name happens. -/
def mergePair (acc extra : Dataset) : Dataset :=
  { default := acc.default ++ extra.default
  , named := acc.named ++ extra.named }

/-- Fold pre-loaded datasets onto a base. The caller does the I/O for
    each one; this fold is pure. -/
def mergeDatasets (base : Dataset) (extras : List Dataset) : Dataset :=
  extras.foldl mergePair base

/-- A quad whose terms the caller has already resolved. `none` for the
    graph means the default graph. -/
structure ResolvedQuad where
  triple : Triple
  graph  : Option Subject
  deriving Repr

/-- Append `t` to the bucket for `name`, or start a new bucket. The
    triple is PREPENDED; `bucketQuads` reverses each bucket at the
    end. -/
def extendNamedBucket (name : Subject) (t : Triple) :
    List NamedGraph → List NamedGraph
  | [] => [{ name := name, graph := [t] }]
  | ng :: rest =>
      if ng.name == name then { ng with graph := t :: ng.graph } :: rest
      else ng :: extendNamedBucket name t rest

def bucketQuadsAcc : List Triple → List NamedGraph → List ResolvedQuad →
    List Triple × List NamedGraph
  | dflt, named, [] => (dflt, named)
  | dflt, named, q :: rest =>
      match q.graph with
      | none => bucketQuadsAcc (q.triple :: dflt) named rest
      | some g => bucketQuadsAcc dflt (extendNamedBucket g q.triple named) rest

def reverseNamedGraph (ng : NamedGraph) : NamedGraph :=
  { ng with graph := ng.graph.reverse }

/-- Partition resolved quads into a dataset, in source order. -/
def bucketQuads (quads : List ResolvedQuad) : Dataset :=
  let (dfltRev, namedRev) := bucketQuadsAcc [] [] quads
  { default := dfltRev.reverse, named := namedRev.map reverseNamedGraph }

/-! ## Build-time checks -/

section Checks

private def wi (s : String) : WfIri :=
  if h : isIri s then ⟨s, h⟩
  else ⟨"http://example.org/not-an-iri", by simp [isIri, String.isEmpty]⟩

private def tr (n : String) : Triple :=
  ⟨.iri (wi ("http://e/" ++ n)), wi "http://e/p", .iri (wi "http://e/o")⟩

private def gA : Subject := .iri (wi "http://e/gA")
private def gB : Subject := .iri (wi "http://e/gB")

/-! ### Merging is BAG semantics: a duplicate survives

`Graph.add` is set-based; `mergePair` is not, and the two must not be
confused. -/

#guard (mergePair ⟨[tr "a"], []⟩ ⟨[tr "a"], []⟩).default.length == 2
#guard (Graph.add (tr "a") [tr "a"]).length == 1

/-! Merging is associative on the default graph and preserves order. -/

#guard (mergeDatasets ⟨[tr "a"], []⟩ [⟨[tr "b"], []⟩, ⟨[tr "c"], []⟩]).default
       == [tr "a", tr "b", tr "c"]
#guard (mergeDatasets Dataset.empty []).default == []

/-! Named-graph lists concatenate without grouping at this level: two
    entries for the same name stay separate, which is why the loader
    calls `bucketQuads` rather than folding `mergePair`. -/

#guard (mergePair ⟨[], [⟨gA, [tr "a"]⟩]⟩ ⟨[], [⟨gA, [tr "b"]⟩]⟩).named.length == 2

/-! ### Bucketing groups by name AND keeps source order -/

private def quads : List ResolvedQuad :=
  [ { triple := tr "1", graph := none }
  , { triple := tr "2", graph := some gA }
  , { triple := tr "3", graph := none }
  , { triple := tr "4", graph := some gB }
  , { triple := tr "5", graph := some gA } ]

private def ds : Dataset := bucketQuads quads

#guard ds.default == [tr "1", tr "3"]
#guard ds.named.length == 2
#guard ds.named.map (·.name) == [gA, gB]
#guard (ds.named.find? (fun ng => ng.name == gA)).map (·.graph)
       == some [tr "2", tr "5"]
#guard (ds.named.find? (fun ng => ng.name == gB)).map (·.graph) == some [tr "4"]

/-! Order is the property an accumulator fold most easily loses: a
    missing reverse still typechecks and still yields the right SET.
    Both the default graph and the `gA` bucket above are checked as
    LISTS, in source order. -/

#guard ds.default != [tr "3", tr "1"]

/-! ### Degenerate inputs -/

#guard (bucketQuads []).default == []
#guard (bucketQuads []).named == []
#guard (bucketQuads [{ triple := tr "1", graph := some gA }]).default == []

/-! A blank node as a graph name — what the Lean dataset model allows
    and the F\* `option string` could not express. -/

#guard (bucketQuads [{ triple := tr "1", graph := some (.bnode "b0") }]).named.length
       == 1
#guard (bucketQuads [{ triple := tr "1", graph := some (.bnode "b0") }]).named.map
         (·.name) == [Subject.bnode "b0"]

end Checks

end L4Factoidal.RDF
