/-
L4Factoidal.RDF.Isomorphism — graph and dataset isomorphism
(blank-node-renaming equivalence), RDF 1.1 Concepts §3.6.

  https://www.w3.org/TR/rdf11-concepts/#section-graph-equality

  "Two RDF graphs G and G' are isomorphic (that is, they have an
   identical form) if there is a bijection M between the sets of nodes
   of the two graphs, such that:
     * M maps blank nodes to blank nodes,
     * M(lit) = lit for all RDF literals lit which are nodes of G,
     * M(iri) = iri for all IRIs iri which are nodes of G,
     * The triple (s, p, o) is in G if and only if the triple
       (M(s), p, M(o)) is in G'."

This is the comparison primitive every W3C evaluation test needs: the
expected and the actual graph are the same graph up to blank-node
labels, which are document-scoped (§3.4) and therefore carry no
meaning of their own.

## Relation to the F* source — READ THIS BEFORE COMPARING

`formal/fstar/RDF.GraphIsomorphism.fst` (200 lines, ZERO `assume val`s)
is what `bin/w3c-runner/w3c_runner.ml` calls. It does NOT search for a
bijection. It reduces isomorphism to CANONICALISATION: both sides are
run through the project's verified RDFC-1.0 canonicaliser
(`RDF.Canonical`, SHA-256 + Hash-N-Degree-Quads) and the canonical
N-Quads strings are byte-compared — rdflib's reduction. Its three-way
outcome (`Iso_Equal` / `Iso_NotEqual` / `Iso_BudgetExceeded`) exists
because RDFC-1.0 carries a Hash-N-Degree-Quads work budget that
pathological blank-node graphs can trip.

This Lean module deliberately takes the OTHER standard route: an
explicit bounded bijection search that PRODUCES THE MAPPING. Reasons:

  1. RDFC-1.0 needs SHA-256, which lives in `L4Factoidal/Crypto/` and
     is another agent's ground; and canonicalisation is a much larger
     port than the comparison primitive that gates the harness.
  2. A canonical-hash shortcut gives a Bool with no witness. A search
     that returns the mapping makes SOUNDNESS a direct check —
     `IsomorphismTheorems.lean` proves the returned mapping really is
     a blank-node bijection carrying `g1` onto `g2`. A hash comparison
     could only be justified by re-proving all of RDFC-1.0.

Two things ARE ported faithfully from the F* module:

  * the three-way outcome type (`IsoOutcome` below), so a work-budget
    trip is a countable, reported event and never a silent pass — the
    F* module's stated reason for having it;
  * the language-tag folding that makes `"a"@en-GB` and `"a"@en-gb`
    compare equal. In the F* source that is an explicit
    `normalize_literal` pass before canonicalisation; here it is
    already inside `Literal.eqb` (`langTagOptionEq` case-folds), which
    is what `Graph.mem` uses, so no separate pass is needed.

`solutions_isomorphic` (the Jena-style SELECT-result reification) is
NOT ported here: it needs the SPARQL solution-mapping type, so it
belongs with the SPARQL side of the port.

## Search bound

Termination is STRUCTURAL, not fuel-based: `searchBijection` recurses
on the list of `g1`'s blank-node labels, which strictly shortens at
every assignment, so the recursion depth is exactly `|bnodes(g1)|` and
no fuel parameter is needed to make the function total. The BREADTH is
what needs a bound: without pruning the search visits at most n!
mappings for n blank nodes. Two bounds apply:

  * signature pruning (`bnodeSig`) restricts each candidate set, and
  * `isoBnodeBudget` refuses outright above 16 blank nodes, reporting
    `IsoOutcome.budgetExceeded` — the analogue of the F* module's
    `Iso_BudgetExceeded`, chosen for the same reason (a W3C evaluation
    graph has a handful of blank nodes; anything far beyond that is
    pathological and must be reported, never silently passed).

The identity mapping is tried FIRST, before any of that, so two graphs
that already agree on labels — the common case for a parser eval test
— cost one set comparison and never enter the search or the budget.
-/
import L4Factoidal.RDF.Graph

namespace L4Factoidal.RDF

/-! ## Blank-node occurrences

Which blank-node labels a term / triple / graph mentions. The
`tripleTerm` case matters: RDF 1.2 lets a blank node sit inside a
triple term, and an isomorphism must rename it there too (the same
place `Term.renameBnodes` recurses). -/

/-- Blank-node labels occurring in a subject. -/
def Subject.bnodes : Subject → List BNodeId
  | .iri _   => []
  | .bnode b => [b]

/-- Blank-node labels occurring in a term, including inside RDF 1.2
triple terms. -/
def Term.bnodes : Term → List BNodeId
  | .iri _            => []
  | .bnode b          => [b]
  | .literal _        => []
  | .tripleTerm s _ o => s.bnodes ++ o.bnodes

/-- Blank-node labels occurring in a triple. -/
def Triple.bnodes (t : Triple) : List BNodeId := t.s.bnodes ++ t.o.bnodes

/-- A ground triple mentions no blank node (RDF 1.1 Concepts §3.6:
ground triples must match exactly under any isomorphism, since `M` is
the identity on IRIs and literals). -/
def Triple.isGround (t : Triple) : Bool := t.bnodes.isEmpty

/-! ## Small label-list utilities

Written out rather than taken from `List.eraseDups` / `List.Nodup`
because the reflexivity proof needs `noDupLabels (dedupLabels l)`, and
a definition shaped for that induction is cheaper than adapting the
core one. Core-Lean only, per the port's zero-dependency rule. -/

/-- Duplicate-free? (Bool, so it can appear inside a decision
procedure.) -/
def noDupLabels : List BNodeId → Bool
  | []      => true
  | b :: bs => !bs.contains b && noDupLabels bs

/-- Remove duplicate labels, keeping the last occurrence of each. -/
def dedupLabels : List BNodeId → List BNodeId
  | []      => []
  | b :: bs =>
      let r := dedupLabels bs
      if r.contains b then r else b :: r

/-- The blank-node labels of a graph, without duplicates. -/
def Graph.bnodes (g : Graph) : List BNodeId :=
  dedupLabels (g.flatMap Triple.bnodes)

/-- The ground sub-graph. -/
def Graph.ground (g : Graph) : Graph := g.filter Triple.isGround

/-- Set-normalise a graph (drop triples already present under the
engine triple equality). Used ONLY to compute blank-node signatures,
never on the path that decides the answer — the answer path is
duplicate-insensitive by construction (see `Graph.setEqB`). -/
def Graph.dedup : Graph → Graph
  | []      => []
  | t :: ts =>
      let r := Graph.dedup ts
      if r.mem t then r else t :: r

/-! ## Triple-set equality

CHOICE, stated once and used everywhere below: a graph is a `List
Triple`, so "the same triple set" is spelled as mutual containment,
with the LEFT side ranged over by ordinary list membership (`t ∈ g1`)
and the RIGHT side tested by `Graph.mem` (the engine triple equality
`Triple.eqb`, which case-folds language tags and canonicalises
`rdf:XMLLiteral` lexical forms). Mixing the two is deliberate: `∈`
enumerates, `Graph.mem` decides. Both directions are stated, so the
relation is symmetric in content even though the two sides are written
differently, and it is insensitive to duplicates and to order — which
is what makes a list a set here. -/

/-- Every triple listed in `g1` is a member of `g2`. -/
def Graph.SubsetOf (g1 g2 : Graph) : Prop := ∀ t ∈ g1, g2.mem t = true

/-- `g1` and `g2` denote the same set of triples. -/
def Graph.SetEq (g1 g2 : Graph) : Prop := g1.SubsetOf g2 ∧ g2.SubsetOf g1

/-- Decision procedure for `Graph.SubsetOf`. -/
def Graph.subsetB (g1 g2 : Graph) : Bool := g1.all (fun t => g2.mem t)

/-- Decision procedure for `Graph.SetEq`. -/
def Graph.setEqB (g1 g2 : Graph) : Bool := g1.subsetB g2 && g2.subsetB g1

/-! ## The specification — RDF 1.1 Concepts §3.6

`M` in the spec is a bijection on NODES that is the identity on IRIs
and literals; equivalently (and this is the form every implementation
uses) it is a bijection on the BLANK NODES, lifted to terms by
`Graph.renameBnodes`. The two clauses "M is a bijection" and "the
triple (s,p,o) is in G iff (M(s),p,M(o)) is in G'" become, in order,
`InjectiveOnBnodes` + `OntoBnodes` and `SetEq`. -/

/-- `f` is injective on the blank nodes `g` actually mentions. (Its
behaviour on labels absent from `g` is irrelevant — no triple sees
it.) -/
def Graph.InjectiveOnBnodes (f : BNodeId → BNodeId) (g : Graph) : Prop :=
  ∀ b1 ∈ g.bnodes, ∀ b2 ∈ g.bnodes, f b1 = f b2 → b1 = b2

/-- `f` covers every blank node of `g2` from a blank node of `g1` —
the surjective half of "bijection between the sets of nodes". -/
def Graph.OntoBnodes (f : BNodeId → BNodeId) (g1 g2 : Graph) : Prop :=
  ∀ b ∈ g2.bnodes, ∃ b', b' ∈ g1.bnodes ∧ f b' = b

/-- **RDF 1.1 Concepts §3.6, graph isomorphism.** There is a
blank-node bijection carrying `g1`'s triple set exactly onto `g2`'s. -/
def Graph.Isomorphic (g1 g2 : Graph) : Prop :=
  ∃ f : BNodeId → BNodeId,
    Graph.InjectiveOnBnodes f g1 ∧
    Graph.OntoBnodes f g1 g2 ∧
    Graph.SetEq (g1.renameBnodes f) g2

/-! ## Blank-node signatures (the pruning)

A candidate for `b₁ ↦ b₂` is only worth trying if `b₁` and `b₂` sit in
structurally indistinguishable triples. The signature of `b` is the
multiset of keys of the triples mentioning `b`, where every OTHER
blank node is written `B`, `b` itself is written `S` (so a self-loop
is distinguishable from an edge to a different blank node), and IRIs
and literals are written out.

Soundness of the pruning: renaming blank nodes changes neither the
predicate, nor any IRI or literal, nor which occurrences are `b`
itself — so a real isomorphism maps `b` only to a blank node with an
equal signature, and restricting candidates this way can never lose a
mapping that the certificate would have accepted... with one
qualification, recorded honestly: the key writes literals out
lexically after folding the language tag, so two literals that
`Literal.eqb` equates through `rdf:XMLLiteral` canonicalisation get
DIFFERENT keys. That can only make the search give up early, never
make it accept — the certificate is the sole arbiter of a `true`
answer — and the identity fast path covers the case in practice. -/

private def dirKey : Option TextDirection → String
  | none      => "-"
  | some .ltr => "l"
  | some .rtl => "r"

/-- Signature key of a subject, relative to the blank node `b`. -/
def Subject.sigKey (b : BNodeId) : Subject → String
  | .iri i   => "I<" ++ i.val ++ ">"
  | .bnode c => if c == b then "S" else "B"

/-- Signature key of a term, relative to the blank node `b`. -/
def Term.sigKey (b : BNodeId) : Term → String
  | .iri i     => "I<" ++ i.val ++ ">"
  | .bnode c   => if c == b then "S" else "B"
  | .literal l =>
      "L<" ++ l.val.lexicalForm ++ ">^<" ++ l.val.datatype.val ++ ">@"
        ++ (l.val.langTag.getD "").toLower ++ dirKey l.val.direction
  | .tripleTerm s p o =>
      "T(" ++ Subject.sigKey b s ++ " I<" ++ p.val ++ "> "
        ++ Term.sigKey b o ++ ")"

/-- Signature key of a whole triple, relative to the blank node `b`. -/
def Triple.sigKey (b : BNodeId) (t : Triple) : String :=
  Subject.sigKey b t.s ++ " I<" ++ t.p.val ++ "> " ++ Term.sigKey b t.o

private def keyCount (x : String) (l : List String) : Nat :=
  (l.filter (fun y => y == x)).length

/-- Multiset equality on signature-key lists (order-insensitive, so no
sort and no `Ord` instance is needed). -/
def keyMultisetEq (l1 l2 : List String) : Bool :=
  l1.length == l2.length && l1.all (fun x => keyCount x l1 == keyCount x l2)

/-- The signature of blank node `b` in `g`: the keys of the
set-normalised triples that mention `b`. -/
def Graph.bnodeSig (g : Graph) (b : BNodeId) : List String :=
  ((Graph.dedup g).filter (fun t => t.bnodes.contains b)).map (Triple.sigKey b)

/-- Precomputed signatures, so the search does not recompute them per
candidate test. -/
def Graph.sigTable (g : Graph) : List (BNodeId × List String) :=
  g.bnodes.map (fun b => (b, g.bnodeSig b))

private def sigLookup (tbl : List (BNodeId × List String)) (b : BNodeId) :
    List String :=
  match tbl.find? (fun p => p.1 == b) with
  | some p => p.2
  | none   => []

/-! ## Candidate mappings

A candidate mapping is an association list of blank-node labels. It is
turned into the `BNodeId → BNodeId` function the specification talks
about by `mapWith`, which is the identity on any label the list does
not mention (labels outside `g1` never reach a triple, so this is
harmless and keeps the function total). -/

/-- The renaming function a candidate mapping denotes. -/
def mapWith (m : List (BNodeId × BNodeId)) (b : BNodeId) : BNodeId :=
  match m.find? (fun p => p.1 == b) with
  | some p => p.2
  | none   => b

def mapDomain (m : List (BNodeId × BNodeId)) : List BNodeId := m.map Prod.fst
def mapImage  (m : List (BNodeId × BNodeId)) : List BNodeId := m.map Prod.snd

/-- The bijection half of the certificate: `m` is a duplicate-free
pairing whose domain is exactly `bs1` and whose image covers `bs2`.
Checked, not assumed — `IsomorphismTheorems.lean` turns each conjunct
into the corresponding clause of `Graph.Isomorphic`. -/
def bijectiveCert (m : List (BNodeId × BNodeId)) (bs1 bs2 : List BNodeId) : Bool :=
  noDupLabels (mapDomain m) &&
  noDupLabels (mapImage m) &&
  m.all (fun p => bs1.contains p.1) &&
  bs1.all (fun b => (mapDomain m).contains b) &&
  bs2.all (fun b => (mapImage m).contains b)

/-- The full certificate for graphs: `m` is a blank-node bijection AND
renaming `g1` by it yields exactly `g2`'s triple set. -/
def Graph.isoCert (m : List (BNodeId × BNodeId)) (g1 g2 : Graph)
    (bs1 bs2 : List BNodeId) : Bool :=
  bijectiveCert m bs1 bs2 && Graph.setEqB (g1.renameBnodes (mapWith m)) g2

/-! ## The search

Backtracking over blank-node assignments. `rem` are the blank nodes of
`g1` still to assign, `avail` the blank nodes of `g2` still unused,
`acc` the pairs chosen so far. Recursion is structural on `rem`, so
the function is total with no fuel argument; `candOk` prunes the
breadth. -/

/-- Bounded backtracking search for a blank-node bijection satisfying
`check`. Parameterised by the acceptance test so that graphs and
datasets share one search (a dataset's test is per-named-graph, which
a flattened graph test could not express). -/
def searchBijection (check : List (BNodeId × BNodeId) → Bool)
    (candOk : BNodeId → BNodeId → Bool)
    (rem avail : List BNodeId) (acc : List (BNodeId × BNodeId)) :
    Option (List (BNodeId × BNodeId)) :=
  match rem with
  | []      => if check acc then some acc else none
  | b :: rest =>
      (avail.filter (candOk b)).findSome? fun c =>
        searchBijection check candOk rest (avail.erase c) ((b, c) :: acc)
termination_by rem.length

/-! ## Outcomes and the top-level decision procedures -/

/-- Port of the F* `iso_outcome`: a work-budget trip is reported, not
silently turned into "not equal". -/
inductive IsoOutcome where
  /-- Same graph up to blank-node renaming. -/
  | equal
  /-- Definitely different. -/
  | notEqual
  /-- Too many blank nodes to search; no answer given. -/
  | budgetExceeded
  deriving DecidableEq, Repr

/-- Refuse to search above this many blank nodes (16! is far past any
W3C evaluation test; beyond it, report rather than guess). -/
def isoBnodeBudget : Nat := 16

/-- The identity mapping on `g`'s blank nodes, as an association
list. -/
def Graph.idMapping (g : Graph) : List (BNodeId × BNodeId) :=
  g.bnodes.map (fun b => (b, b))

/-- Everything after the identity fast path: cheap necessary
conditions, the budget refusal, then the backtracking search. Its
result is a CANDIDATE — `Graph.isomorphismMap?` is what certifies
it. -/
def Graph.isoSearchStep (g1 g2 : Graph) : Option (List (BNodeId × BNodeId)) :=
  if g1.bnodes.length != g2.bnodes.length then none
  else if !Graph.setEqB g1.ground g2.ground then none
  else if g1.bnodes.length > isoBnodeBudget then none
  else
    searchBijection
      (fun m => Graph.isoCert m g1 g2 g1.bnodes g2.bnodes)
      (fun b1 b2 => keyMultisetEq (sigLookup g1.sigTable b1)
                                  (sigLookup g2.sigTable b2))
      g1.bnodes g2.bnodes []

/-- Candidate mapping: the identity first (the common eval-test case,
one set comparison, no search and no budget), then the search. -/
def Graph.isoSearch (g1 g2 : Graph) : Option (List (BNodeId × BNodeId)) :=
  if Graph.isoCert g1.idMapping g1 g2 g1.bnodes g2.bnodes
  then some g1.idMapping
  else Graph.isoSearchStep g1 g2

/-- The mapping search for graphs. Returns the WITNESS, not just a
Bool, and certifies it on the way out, so soundness needs NOTHING from
the search — only that whatever comes back passes `Graph.isoCert`. -/
def Graph.isomorphismMap? (g1 g2 : Graph) :
    Option (List (BNodeId × BNodeId)) :=
  match Graph.isoSearch g1 g2 with
  | some m => if Graph.isoCert m g1 g2 g1.bnodes g2.bnodes then some m else none
  | none   => none

/-- Graph isomorphism as a Bool (RDF 1.1 Concepts §3.6). -/
def Graph.isomorphic? (g1 g2 : Graph) : Bool :=
  (g1.isomorphismMap? g2).isSome

/-- Graph comparison with the F* module's three-way outcome. -/
def Graph.isomorphicOutcome (g1 g2 : Graph) : IsoOutcome :=
  if (g1.isomorphismMap? g2).isSome then .equal
  else if g1.bnodes.length > isoBnodeBudget || g2.bnodes.length > isoBnodeBudget
  then .budgetExceeded
  else .notEqual

/-! ## Datasets — RDF 1.1 Concepts §4 / §3.6

Blank nodes are scoped to the DATASET, not to each graph: one
bijection must work for the default graph and for every named graph at
once. So the search runs over the dataset's whole blank-node set,
while the acceptance test is per-graph.

Named graphs are matched BY NAME (IRI equality, via
`Dataset.lookupNamed`) — never by isomorphism of the name. This port's
`NamedGraph.name` is an `Iri`, so blank-node graph names, which
RDF 1.1 §4 permits, cannot be expressed here at all; the F* source has
the same shape (`ng_name` is an IRI), so nothing is lost relative to
it. Should graph names ever become terms, the search would have to
range over them too. -/

/-- Every blank-node label of a dataset, default graph and named
graphs together. -/
def Dataset.bnodes (ds : Dataset) : List BNodeId :=
  dedupLabels
    (ds.default.flatMap Triple.bnodes ++
     ds.named.flatMap (fun ng => ng.graph.flatMap Triple.bnodes))

/-- All triples of a dataset in one list — used ONLY for signature
pruning, where graph boundaries do not matter. -/
def Dataset.flatten (ds : Dataset) : Graph :=
  ds.default ++ ds.named.flatMap (fun ng => ng.graph)

/-- Rename every blank node of a dataset. -/
def Dataset.renameBnodes (f : BNodeId → BNodeId) (ds : Dataset) : Dataset :=
  { default := ds.default.renameBnodes f,
    named   := ds.named.map (fun ng => { ng with graph := ng.graph.renameBnodes f }) }

/-- Distinct graph names — the well-formedness condition of RDF 1.1
Concepts §4 (a dataset holds at most one graph per name). The Lean
type does not enforce it, so `Dataset.isomorphic?_refl` takes it as a
hypothesis rather than pretending: `Dataset.lookupNamed` returns the
FIRST graph carrying a name, so a value listing two different graphs
under one name is not even equal to itself under name matching. -/
def Dataset.namesNoDup (ds : Dataset) : Bool :=
  noDupLabels (ds.named.map (fun ng => ng.name))

/-- The two datasets name the same graphs. -/
def Dataset.namesMatchB (ds1 ds2 : Dataset) : Bool :=
  ds1.named.all (fun ng => (ds2.lookupNamed ng.name).isSome) &&
  ds2.named.all (fun ng => (ds1.lookupNamed ng.name).isSome)

/-- Graph-by-graph triple-set equality after renaming `ds1` by `m`. -/
def Dataset.checkMapping (m : List (BNodeId × BNodeId)) (ds1 ds2 : Dataset) : Bool :=
  Graph.setEqB (ds1.default.renameBnodes (mapWith m)) ds2.default &&
  ds1.named.all (fun ng =>
    match ds2.lookupNamed ng.name with
    | some g2 => Graph.setEqB (ng.graph.renameBnodes (mapWith m)) g2
    | none    => false) &&
  Dataset.namesMatchB ds1 ds2

/-- The full certificate for datasets. -/
def Dataset.isoCert (m : List (BNodeId × BNodeId)) (ds1 ds2 : Dataset)
    (bs1 bs2 : List BNodeId) : Bool :=
  bijectiveCert m bs1 bs2 && Dataset.checkMapping m ds1 ds2

/-- Specification counterpart of `Dataset.checkMapping`. -/
def Dataset.SetEq (ds1 ds2 : Dataset) : Prop :=
  Graph.SetEq ds1.default ds2.default ∧
  (∀ ng ∈ ds1.named, ∃ g2, ds2.lookupNamed ng.name = some g2 ∧
                            Graph.SetEq ng.graph g2) ∧
  (∀ ng ∈ ds2.named, (ds1.lookupNamed ng.name).isSome = true)

def Dataset.InjectiveOnBnodes (f : BNodeId → BNodeId) (ds : Dataset) : Prop :=
  ∀ b1 ∈ ds.bnodes, ∀ b2 ∈ ds.bnodes, f b1 = f b2 → b1 = b2

def Dataset.OntoBnodes (f : BNodeId → BNodeId) (ds1 ds2 : Dataset) : Prop :=
  ∀ b ∈ ds2.bnodes, ∃ b', b' ∈ ds1.bnodes ∧ f b' = b

/-- **Dataset isomorphism**: one blank-node bijection, dataset-wide,
carrying the default graph onto the default graph and each named graph
onto the graph of the same name. -/
def Dataset.Isomorphic (ds1 ds2 : Dataset) : Prop :=
  ∃ f : BNodeId → BNodeId,
    Dataset.InjectiveOnBnodes f ds1 ∧
    Dataset.OntoBnodes f ds1 ds2 ∧
    Dataset.SetEq (ds1.renameBnodes f) ds2

/-- The identity mapping on a dataset's blank nodes. -/
def Dataset.idMapping (ds : Dataset) : List (BNodeId × BNodeId) :=
  ds.bnodes.map (fun b => (b, b))

/-- Everything after the identity fast path, for datasets. -/
def Dataset.isoSearchStep (ds1 ds2 : Dataset) :
    Option (List (BNodeId × BNodeId)) :=
  if ds1.bnodes.length != ds2.bnodes.length then none
  else if !Dataset.namesMatchB ds1 ds2 then none
  else if ds1.bnodes.length > isoBnodeBudget then none
  else
    searchBijection
      (fun m => Dataset.isoCert m ds1 ds2 ds1.bnodes ds2.bnodes)
      (fun b1 b2 => keyMultisetEq (sigLookup ds1.flatten.sigTable b1)
                                  (sigLookup ds2.flatten.sigTable b2))
      ds1.bnodes ds2.bnodes []

def Dataset.isoSearch (ds1 ds2 : Dataset) : Option (List (BNodeId × BNodeId)) :=
  if Dataset.isoCert ds1.idMapping ds1 ds2 ds1.bnodes ds2.bnodes
  then some ds1.idMapping
  else Dataset.isoSearchStep ds1 ds2

/-- The mapping search for datasets. Same shape as the graph one; the
signature pruning uses the flattened dataset, the certificate does
not. -/
def Dataset.isomorphismMap? (ds1 ds2 : Dataset) :
    Option (List (BNodeId × BNodeId)) :=
  match Dataset.isoSearch ds1 ds2 with
  | some m =>
      if Dataset.isoCert m ds1 ds2 ds1.bnodes ds2.bnodes then some m else none
  | none   => none

/-- Dataset isomorphism as a Bool. -/
def Dataset.isomorphic? (ds1 ds2 : Dataset) : Bool :=
  (ds1.isomorphismMap? ds2).isSome

/-- Dataset comparison with the three-way outcome. -/
def Dataset.isomorphicOutcome (ds1 ds2 : Dataset) : IsoOutcome :=
  if (ds1.isomorphismMap? ds2).isSome then .equal
  else if ds1.bnodes.length > isoBnodeBudget || ds2.bnodes.length > isoBnodeBudget
  then .budgetExceeded
  else .notEqual

end L4Factoidal.RDF
