/-
L4Factoidal.SPARQL.PropertyPath — SPARQL 1.1 property paths (§9, §18.4).

Port of `formal/fstar/SPARQL11.Algebra.fst` Part 4 (`property_path`)
and Part 13 (`eval_property_path`).

A property path denotes a set of (subject, object) PAIRS over a graph,
independent of any solution mapping; the algebra layer
(`SPARQL.Algebra`) turns those pairs into solution mappings by matching
them against the pattern's subject and object positions
(`pathResultToSolutions`).

WHAT IS PORTED
  * §9.1 path syntax: `iri`, `^p` (inverse), `p1/p2` (sequence),
    `p1|p2` (alternative), `p*`, `p+`, `p?`, and the negated property
    set `!(:a|:b|^:c)`;
  * §18.4 / §9.3 evaluation: one-step lookup, inverse, sequence,
    alternative, and the reflexive/transitive closures.

TERMINATION. `evalPath` recurses STRUCTURALLY on the path expression;
the two closure forms (`zeroOrMore`, `oneOrMore`) reach their fixpoint
with an EXPLICIT fuel counter (`pathFixpoint`), seeded — as in the F*
source — with the number of distinct nodes in the graph. That is a
bound, not an approximation: a chain of `n` nodes needs at most `n`
extension rounds, and the loop also stops early as soon as a round adds
nothing. No `partial def`, no well-founded recursion.

THE §18.2.2.5 REFLEXIVITY POINT (issue #66 in the F* tree) is NOT here:
`graphNodes` only lists nodes that occur in some triple, so a constant
IRI written in the query but absent from the data would miss its
reflexive `(c, c)` pair. The algebra layer adds those missing pairs for
`zeroOrMore` / `zeroOrOne` patterns, where it can see the pattern's
constants — see `SPARQL.Algebra`'s `propertyPath` arm.
-/
import L4Factoidal.RDF.Graph

namespace L4Factoidal.SPARQL

open L4Factoidal.RDF

/-! ## Path syntax — SPARQL 1.1 §9.1 -/

/-- A SPARQL 1.1 property path expression (§9.1 "Property Path
Syntax Forms"). -/
inductive PropertyPath where
  /-- `iri` — a one-step predicate path. -/
  | iri         (i : WfIri)
  /-- `^path` — inverse path (§9.1). -/
  | inverse     (p : PropertyPath)
  /-- `path1 / path2` — sequence path. -/
  | sequence    (p1 p2 : PropertyPath)
  /-- `path1 | path2` — alternative path. -/
  | alternative (p1 p2 : PropertyPath)
  /-- `path*` — zero or more (reflexive transitive closure). -/
  | zeroOrMore  (p : PropertyPath)
  /-- `path+` — one or more (transitive closure). -/
  | oneOrMore   (p : PropertyPath)
  /-- `path?` — zero or one. -/
  | zeroOrOne   (p : PropertyPath)
  /-- `!(:a|:b|^:c)` — negated property set. -/
  | negatedSet  (ps : List PropertyPath)
  deriving Repr

/-! ## Path results — the (subject, object) pair relation -/

/-- The value a path denotes over a graph: a list of node pairs. -/
abbrev PathResult := List (Term × Term)

/-- Pair equality through the engine term equality (`Term.eqb`) — port
of `path_pair_eq`. -/
def pathPairEq (p1 p2 : Term × Term) : Bool :=
  p1.1.eqb p2.1 && p1.2.eqb p2.2

/-- Deduplicate a path result, keeping the LAST occurrence of each
pair — port of `list_dedup_by path_pair_eq`. -/
def dedupPath : PathResult → PathResult
  | []      => []
  | x :: xs => if xs.any (pathPairEq x) then dedupPath xs else x :: dedupPath xs

/-- Is this term usable as a subject? An inverse path turns objects
into subjects, and a literal cannot be one — port of
`is_not_literal`. -/
def isNotLiteral : Term → Bool
  | .literal _ => false
  | _          => true

/-- Every node mentioned in the graph, deduplicated — the domain the
reflexive part of `p*` / `p?` ranges over (§9.3). Port of
`graph_nodes`. -/
def graphNodes (g : Graph) : List Term :=
  let subjects := g.map (fun t => t.s.toTerm)
  let objects  := g.map (fun t => t.o)
  (dedupPath ((subjects ++ objects).map (fun n => (n, n)))).map Prod.fst

/-- The direct (non-inverse) IRIs of a negated property set — port of
`negated_direct_iris`. -/
def negatedDirectIris : List PropertyPath → List WfIri
  | []                => []
  | .iri i :: rest    => i :: negatedDirectIris rest
  | _ :: rest         => negatedDirectIris rest

/-- The inverse IRIs of a negated property set (`^:c` members) — port
of `negated_inverse_iris`. -/
def negatedInverseIris : List PropertyPath → List WfIri
  | []                        => []
  | .inverse (.iri i) :: rest => i :: negatedInverseIris rest
  | _ :: rest                 => negatedInverseIris rest

/-- Membership of an IRI in a list — port of `iri_in_list`. -/
def iriInList (i : WfIri) (iris : List WfIri) : Bool :=
  iris.any (fun j => j == i)

/-! ## Closure by bounded iteration

`pathExtend step current` is one round of "follow one more `step`
edge from every pair already reached". `pathFixpoint` repeats it until
the result stops growing, or until the fuel runs out. Both bounds are
sound: the pair set is a subset of nodes × nodes, so it can grow at
most finitely often, and the caller seeds the fuel with the node
count (the length of the longest simple chain). -/

/-- One extension round: compose `current` with one more `step` edge
and merge the new pairs in. -/
def pathExtend (step current : PathResult) : PathResult :=
  let newPairs := current.flatMap (fun p1 =>
    step.filterMap (fun p2 => if p1.2.eqb p2.1 then some (p1.1, p2.2) else none))
  dedupPath (current ++ newPairs)

/-- Iterate `pathExtend` to a fixed point, bounded by `fuel`. Stops
early when a round adds no new pairs (the F* source's
`length next = length current` test). -/
def pathFixpoint (step : PathResult) : PathResult → Nat → PathResult
  | current, 0          => current
  | current, Nat.succ n =>
      let next := pathExtend step current
      if next.length == current.length then current
      else pathFixpoint step next n

/-! ## Path evaluation — SPARQL 1.1 §18.4 / §9.3 -/

/-- `eval(path, G)` — the pair relation a path denotes over a graph.
Structurally recursive on the path; the two closure forms use
`pathFixpoint` with a node-count fuel bound. Port of
`eval_property_path`. -/
def evalPath : PropertyPath → Graph → PathResult
  -- §9.3 PredicatePath: { (s,o) | (s, iri, o) ∈ G }.
  | .iri i, g =>
      g.filterMap (fun t => if t.p == i then some (t.s.toTerm, t.o) else none)
  -- §9.1 InversePath: the converse relation, dropping pairs whose new
  -- subject would be a literal.
  | .inverse p, g =>
      (evalPath p g).filterMap (fun pr =>
        if isNotLiteral pr.2 then some (pr.2, pr.1) else none)
  -- §9.1 SequencePath: relational composition. Bag semantics — two
  -- distinct routes through the middle node give two pairs.
  | .sequence p1 p2, g =>
      let r1 := evalPath p1 g
      let r2 := evalPath p2 g
      r1.flatMap (fun a =>
        r2.filterMap (fun b => if a.2.eqb b.1 then some (a.1, b.2) else none))
  -- §9.1 AlternativePath: union, bag semantics.
  | .alternative p1 p2, g => evalPath p1 g ++ evalPath p2 g
  -- §9.1 ZeroOrOnePath: the reflexive pairs over the graph's nodes,
  -- plus one step.
  | .zeroOrOne p, g =>
      dedupPath ((graphNodes g).map (fun n => (n, n)) ++ evalPath p g)
  -- §9.1 ZeroOrMorePath: reflexive transitive closure.
  | .zeroOrMore p, g =>
      let nodes := graphNodes g
      let step  := evalPath p g
      pathFixpoint step (dedupPath (nodes.map (fun n => (n, n)) ++ step)) nodes.length
  -- §9.1 OneOrMorePath: transitive closure (no reflexive seed).
  | .oneOrMore p, g =>
      let nodes := graphNodes g
      let step  := evalPath p g
      pathFixpoint step step nodes.length
  -- §9.1 NegatedPropertySet. A set containing only inverse members
  -- contributes no forward pairs, and vice versa — the F* source's
  -- `has_direct` / `has_inverse` gates, kept verbatim.
  | .negatedSet ps, g =>
      let excludedDirect  := negatedDirectIris ps
      let excludedInverse := negatedInverseIris ps
      let hasDirect  := !excludedDirect.isEmpty
      let hasInverse := !excludedInverse.isEmpty
      let directPairs :=
        if hasInverse && !hasDirect then []
        else g.filterMap (fun t =>
          if iriInList t.p excludedDirect then none else some (t.s.toTerm, t.o))
      let inversePairs :=
        if hasDirect && !hasInverse then []
        else g.filterMap (fun t =>
          if iriInList t.p excludedInverse then none else some (t.o, t.s.toTerm))
      directPairs ++ inversePairs

end L4Factoidal.SPARQL
