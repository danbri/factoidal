/-
L4Factoidal.RDFS.SchemaSplit — close the class and property hierarchy
once, then push it at the data.

Port of `formal/fstar/RDFS.SchemaSplit.fst` (808 lines).

## Why the split exists

The RDFS closure runs one fixed-point loop over the whole graph. Rows
rdfs11 and rdfs5 — the transitivity of `rdfs:subClassOf` and
`rdfs:subPropertyOf` — are the only recursive rows, and they re-derive
the entire transitive closure on every round. At round `k` the graph
already holds a quadratic number of subclass edges, the row iterates all
of them, and each does a successor lookup yielding a linear number of
hits: a cubic number of emissions per round to produce a quadratic
answer. On a pure-schema chain the F\* measurement was 15.2 seconds at
160 classes.

A production reasoner closes the hierarchy ONCE, on the schema alone,
then pushes the result at the instance data in a single pass. That is
what this module does, with a checked side condition and a fallback to
the untouched general loop.

## The trap: RDFS is reflective

A graph may say

    :p rdfs:subPropertyOf rdfs:subClassOf .
    :A :p :B .

and rdfs7 then derives `:A rdfs:subClassOf :B` — an ORDINARY DATA TRIPLE
HAS INJECTED A NEW SCHEMA EDGE. Any design that closes the schema first
and never revisits it loses that derivation.

So the side condition below blocks every first-order route by which a
non-schema premise can produce a schema edge. The F\* banner carries the
row-by-row enumeration that derives the three clauses and the argument
that the enumeration closes; it is not repeated here, and anyone
extending the rule table has to re-run it there.

## The enumeration is NOT load-bearing at runtime

That is the part worth carrying over. The enumeration is a reasoning
artefact, and this project's record on this rule set is that confident
reasoning about it gets caught out by measurement. So the dispatcher
does not trust it: it runs the fast path and then CHECKS the one
property the enumeration exists to establish — that the loop derived no
schema edge the pre-computed closure did not already carry — and
discards the result and takes the general loop if that check fails.

`schemaStableCheck` is the stated hypothesis of the equivalence claim,
not the runtime gate. Every uncertainty falls back to the general loop,
never forward into the fast path.

## What the Lean tree splits differently

The F\* dispatcher wraps `rdfs_closure_with_reflexivity`, whose
reflexivity harvest is part of the same module as the twelve rows. In
the Lean tree the six recursive rows are `RDFS.Closure` and the
reflexivity harvest is in `RDFS.FullClosure`, so the dispatcher here
wraps `RDFS.closureFix` — the ρdf core closure — and the F\* module's
two-pass reflexivity shape has no counterpart to reproduce. The
side condition, the schema walk, the no-transitivity loop and the
post-hoc check all carry over unchanged.
-/
import L4Factoidal.RDFS.Closure
import L4Factoidal.RDFS.Vocabulary

namespace L4Factoidal.RDFS

open L4Factoidal.RDF

/-! ## 1. The side condition -/

/-- The ρdf control vocabulary: the five IRIs the RDFS rule table reads
in PREDICATE position. A `rdfs:subPropertyOf` declaration pointing at any
of them re-routes ordinary data into the rule machinery. -/
def isControlIri (i : WfIri) : Bool :=
  i == rdfsSubClassOf || i == rdfsSubPropertyOf ||
  i == rdfsDomain || i == rdfsRange || i == rdfType

/-- The three type-objects whose membership emits a schema edge: rdfs8
fires on `rdfs:Class`, rdfs13 on `rdfs:Datatype`, and the reflexivity
harvest on `rdfs:Class` and `rdf:Property`. -/
def isSchemaClassIri (i : WfIri) : Bool :=
  i == rdfsClass || i == rdfsDatatype || i == rdfProperty

def objNotControl : Term → Bool
  | .iri i => !isControlIri i
  | _ => true

def objNotSchemaClass : Term → Bool
  | .iri i => !isSchemaClassIri i
  | _ => true

/-- Clause A. No `rdfs:subPropertyOf` declaration may target a control
predicate, so rdfs7 can never mint a schema edge, an `rdf:type` triple,
or a domain or range declaration. -/
def noControlAliasing (t : Triple) : Bool :=
  if t.p == rdfsSubPropertyOf then objNotControl t.o else true

/-- Clause B. No `rdfs:domain` or `rdfs:range` declaration may name one
of the three schema classes, so rdfs2 and rdfs3 can never mint a premise
for rdfs8, rdfs13 or the reflexivity harvest. -/
def noMetaDomainRange (t : Triple) : Bool :=
  if t.p == rdfsDomain || t.p == rdfsRange then objNotSchemaClass t.o else true

/-- Clause C. No `rdfs:subClassOf` edge may point AT one of the three
schema classes, so rdfs9 can never lift an ordinary individual into
one. -/
def noMetaSuperclass (t : Triple) : Bool :=
  if t.p == rdfsSubClassOf then objNotSchemaClass t.o else true

def schemaStableTriple (t : Triple) : Bool :=
  noControlAliasing t && noMetaDomainRange t && noMetaSuperclass t

/-- The declarative side condition: the hypothesis under which the fast
path is claimed equivalent to the general fixed point. -/
def SchemaStable (g : Graph) : Prop :=
  ∀ t ∈ g, schemaStableTriple t = true

/-- The detector. One linear pass — no index, no closure. -/
def schemaStableCheck (g : Graph) : Bool := g.all schemaStableTriple

/-! ## 2. The detector decides exactly the declarative condition

Soundness is the direction a caller relies on. Completeness rules out a
detector that is merely `false`, which would make the fast branch dead
code and the equivalence claim vacuous in practice. -/

theorem schemaStableCheck_sound {g : Graph} (h : schemaStableCheck g = true) :
    SchemaStable g := by
  intro t ht
  exact (List.all_eq_true.mp h) t ht

theorem schemaStableCheck_complete {g : Graph} (h : SchemaStable g) :
    schemaStableCheck g = true :=
  List.all_eq_true.mpr h

/-! ## 3. The schema walk

One reachability walk per source, along one relation. -/

def isSchemaEdge (t : Triple) : Bool :=
  t.p == rdfsSubClassOf || t.p == rdfsSubPropertyOf

/-- A triple's object, when it can stand in subject position. -/
def termToSubject? : Term → Option Subject
  | .iri i => some (.iri i)
  | .bnode b => some (.bnode b)
  | _ => none

/-- The subject-eligible successors of `s` under `rel`, deduplicated —
what makes each node enter the frontier at most once. -/
def succSubjects (g : Graph) (rel : WfIri) (s : Subject) : List Subject :=
  ((objectsOf g s rel).filterMap termToSubject?).foldl
    (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- One `rel`-reachability walk.

FUEL IS A CHECKED BOUND, NOT A SILENT ONE. The second component is
`false` exactly when the budget ran out with work left, and every caller
up to the dispatcher turns that into a fallback. A silently truncated
walk would return an incomplete hierarchy that looks complete. -/
def scBfs (g : Graph) (rel : WfIri) : Nat → List Subject → List Subject →
    List Subject × Bool
  | _, [], visited => (visited, true)
  | 0, _ :: _, visited => (visited, false)
  | fuel + 1, s :: rest, visited =>
      let fresh := (succSubjects g rel s).filter (fun x => !visited.contains x)
      scBfs g rel fuel (rest ++ fresh) (visited ++ fresh)

/-- Everything reachable from `a` along one or more `rel` edges. -/
def scReach (g : Graph) (rel : WfIri) (fuel : Nat) (a : Subject) :
    List Subject × Bool :=
  let start := succSubjects g rel a
  scBfs g rel fuel start start

/-- The transitive closure of a relation whose composition needs the
intermediate term to stand in subject position is

    T(a) = succ(a) ∪ { c | ∃ x ∈ Reach(a), (x, rel, c) }

and `scReach` returns `Reach(a)`. The first term is already an asserted
edge, so only the second is emitted. -/
def emitEdge (a : Subject) (rel : WfIri) (acc : Graph) (o : Term) : Graph :=
  acc ++ [({ s := a, p := rel, o := o } : Triple)]

def emitFromNode (g : Graph) (rel : WfIri) (a : Subject) (acc : Graph)
    (x : Subject) : Graph :=
  (objectsOf g x rel).foldl (emitEdge a rel) acc

def scEdgesFor (g : Graph) (rel : WfIri) (fuel : Nat) (acc : Graph × Bool)
    (a : Subject) : Graph × Bool :=
  let (reached, ok) := scReach g rel fuel a
  (reached.foldl (emitFromNode g rel a) acc.1, acc.2 && ok)

/-- The distinct subjects of `rel` triples — the sources of the walk. -/
def relSubjects (g : Graph) (rel : WfIri) : List Subject :=
  (g.filter (fun t => t.p == rel)).foldl
    (fun acc t => if acc.contains t.s then acc else acc ++ [t.s]) []

/-- DENSITY GUARD. The walk's visited test is a list scan, so its cost
is quadratic in the size of a reached set. On a SPARSE hierarchy — every
real vocabulary — reached sets are paths and the walk is cheap. On an
ALREADY-CLOSED hierarchy, the shape you get by feeding a materialised
graph back in, every reached set is the whole component and the walk is
slower than the loop it replaces. Rather than gamble, notice the shape
and take the general loop. Falling back costs only the speedup. -/
def schemaDense (g : Graph) : Bool :=
  let edges := (g.filter isSchemaEdge).length
  let srcs := (relSubjects g rdfsSubClassOf).length
              + (relSubjects g rdfsSubPropertyOf).length
  edges > 8 * srcs + 64

/-- The closed schema fragment of `g`, plus a completeness flag. -/
def schemaClosedEdges (g : Graph) : Graph × Bool :=
  let fuel := g.length + 2
  let acc1 := (relSubjects g rdfsSubClassOf).foldl
                (scEdgesFor g rdfsSubClassOf fuel) (([], true) : Graph × Bool)
  (relSubjects g rdfsSubPropertyOf).foldl (scEdgesFor g rdfsSubPropertyOf fuel) acc1

/-! ## 4. The instance loop: the closure step without rdfs11 and rdfs5

`RDFS.stepConclusions` with the two transitivity rows removed and
nothing else changed — same rows, same order. With the schema fragment
closed before the loop starts, rdfs11 and rdfs5 have no unsatisfied
instance left to fire on, so dropping them removes only re-derivation. -/

def stepConclusionsNoTrans (g : Graph) : List Triple :=
  g.flatMap (rdfs7For g) ++
  g.flatMap (rdfs2For g) ++
  g.flatMap (rdfs3For g) ++
  g.flatMap (rdfs9For g)

def stepNoTrans (g : Graph) : Graph := addAll g (stepConclusionsNoTrans g)

def closureNoTrans (g : Graph) : Nat → Graph
  | 0 => g
  | n + 1 =>
      let g' := stepNoTrans g
      if g'.length = g.length then g else closureNoTrans g' n

/-! ## 5. The dispatcher

Every uncertainty falls back to the untouched general loop:

1. the schema fragment is already dense (the performance guard);
2. a reachability walk exhausted its step budget;
3. the fast pass failed its post-hoc injection check.

The a-priori `schemaStableCheck` is NOT a gate. It is the stated
hypothesis of the equivalence claim — the condition under which reason 3
provably never fires — and it is exported for callers and tests. Gating
on it as well would cost the fast path on vocabularies whose syntactic
violation never actually injects anything, and the post-hoc check is
strictly stronger because it does not depend on the enumeration being
complete. -/

def countSchemaEdges (g : Graph) : Nat := (g.filter isSchemaEdge).length

/-- Run the no-transitivity loop and check that it derived no schema
edge the pre-computed closure did not already carry. -/
def fastPass (g : Graph) (fuel : Nat) : Graph × Bool :=
  let before := countSchemaEdges g
  let r := closureNoTrans g fuel
  (r, countSchemaEdges r == before)

def closureDispatch (g : Graph) (fuel : Nat) : Graph :=
  if schemaDense g then closure g fuel
  else
    let (extra, ok) := schemaClosedEdges g
    if !ok then closure g fuel
    else
      let seeded := addAll g extra
      let (r, okFast) := fastPass seeded fuel
      if okFast then r else closure g fuel

/-- The dispatcher at the same fuel budget `closureFix` uses. -/
def closureFixDispatch (g : Graph) : Graph := closureDispatch g (closureFuelBound g)

/-! ## 6. Proofs

The walk's shape is pinned, because a wrong predicate would silently
move data into the schema fragment and a wrong subject would fabricate
an edge nothing licenses. -/

/-- Every triple `emitEdge` adds carries the walked predicate and the
walked source, and it preserves that of everything already there. -/
theorem emitEdge_shape (a : Subject) (rel : WfIri) (acc : Graph) (o : Term)
    (h : ∀ u ∈ acc, u.p = rel ∧ u.s = a) :
    ∀ u ∈ emitEdge a rel acc o, u.p = rel ∧ u.s = a := by
  intro u hu
  rcases List.mem_append.mp hu with h' | h'
  · exact h u h'
  · rcases List.mem_singleton.mp h' with rfl
    exact ⟨rfl, rfl⟩

theorem emitFromNode_shape (g : Graph) (rel : WfIri) (a : Subject) (acc : Graph)
    (x : Subject) (h : ∀ u ∈ acc, u.p = rel ∧ u.s = a) :
    ∀ u ∈ emitFromNode g rel a acc x, u.p = rel ∧ u.s = a := by
  unfold emitFromNode
  induction objectsOf g x rel generalizing acc with
  | nil => simpa using h
  | cons o os ih => exact ih _ (emitEdge_shape a rel acc o h)

/-- The walk never drops a node it has already justified. -/
theorem scBfs_visited_grows (g : Graph) (rel : WfIri) :
    ∀ (fuel : Nat) (frontier visited : List Subject),
      visited.Sublist (scBfs g rel fuel frontier visited).1
  | _, [], visited => by simp [scBfs]
  | 0, _ :: _, visited => by simp [scBfs]
  | fuel + 1, s :: rest, visited => by
      simp only [scBfs]
      exact (List.sublist_append_left visited _).trans
        (scBfs_visited_grows g rel fuel _ _)

/-! ## 7. Build-time checks -/

section Checks

private def iriW (s : String) : WfIri :=
  if h : isIri s then ⟨s, h⟩ else ⟨"http://e.org/", by decide⟩

private def cA : WfIri := iriW "http://e.org/A"
private def cB : WfIri := iriW "http://e.org/B"
private def cC : WfIri := iriW "http://e.org/C"
private def pP : WfIri := iriW "http://e.org/p"
private def iI : WfIri := iriW "http://e.org/i"

private def sub (a b : WfIri) : Triple := ⟨.iri a, rdfsSubClassOf, .iri b⟩

/-! ### The witness pair

A side condition nothing satisfies is worthless, and one everything
satisfies gates nothing. Both directions are exhibited. -/

private def witnessStable : Graph :=
  [ sub cA cB, sub cB cC, ⟨.iri iI, rdfType, .iri cA⟩ ]

/-- The owner's reflective example: a `subPropertyOf` declaration
pointing at `rdfs:subClassOf`, which lets an ordinary data triple inject
a schema edge. -/
private def witnessReflective : Graph :=
  [ ⟨.iri pP, rdfsSubPropertyOf, .iri rdfsSubClassOf⟩,
    ⟨.iri cA, pP, .iri cB⟩ ]

#guard schemaStableCheck witnessStable
#guard !schemaStableCheck witnessReflective

/-! And each clause is exercised on its own, so a detector that only
happened to catch clause A would fail here. -/

#guard !schemaStableCheck [⟨.iri pP, rdfsDomain, .iri rdfsClass⟩]        -- clause B
#guard !schemaStableCheck [⟨.iri pP, rdfsRange, .iri rdfProperty⟩]       -- clause B
#guard !schemaStableCheck [⟨.iri cA, rdfsSubClassOf, .iri rdfsDatatype⟩] -- clause C
#guard schemaStableCheck [⟨.iri cA, rdfsSubClassOf, .iri cB⟩]            -- ordinary

/-! ### The walk computes the transitive closure of a chain -/

private def chain3 : Graph := [sub cA cB, sub cB cC]

#guard (schemaClosedEdges chain3).2
#guard Graph.mem (sub cA cC) (schemaClosedEdges chain3).1

/-! It emits only what the reachability licenses — no `A ⊑ A`, and
nothing outside the two schema relations. -/

#guard !Graph.mem (sub cA cA) (schemaClosedEdges chain3).1
#guard (schemaClosedEdges chain3).1.all isSchemaEdge

/-! ### A CYCLE terminates and closes -/

private def cyc3 : Graph := [sub cA cB, sub cB cC, sub cC cA]

#guard (schemaClosedEdges cyc3).2
#guard Graph.mem (sub cA cA) (schemaClosedEdges cyc3).1
#guard Graph.mem (sub cB cA) (schemaClosedEdges cyc3).1

/-! ### The dispatcher agrees with the general closure, as a SET

This is the property the F\* module states in prose and checks by
measurement rather than proving. It is checked here the same way, at
several shapes — including one that VIOLATES the side condition, where
the post-hoc check is what has to catch the injection and fall back. -/

private def sameSet (a b : Graph) : Bool :=
  a.all (fun t => Graph.mem t b) && b.all (fun t => Graph.mem t a)

private def agrees (g : Graph) : Bool :=
  sameSet (closureFixDispatch g) (closureFix g)

#guard agrees witnessStable
#guard agrees chain3
#guard agrees cyc3
#guard agrees witnessReflective
#guard agrees []
#guard agrees [⟨.iri iI, rdfType, .iri cA⟩]

/-! A four-class chain with instance data, which is the shape the split
exists for: the hierarchy is closed once and pushed at the data. -/

private def chainWithData : Graph :=
  [ sub cA cB, sub cB cC, sub cC (iriW "http://e.org/D"),
    ⟨.iri iI, rdfType, .iri cA⟩,
    ⟨.iri pP, rdfsDomain, .iri cA⟩,
    ⟨.iri (iriW "http://e.org/x"), pP, .iri (iriW "http://e.org/y")⟩ ]

#guard agrees chainWithData

/-! And the agreement is not vacuous: the closure really does derive
rows, and the dispatcher really does take its fast branch here. -/

#guard (closureFix chainWithData).length > chainWithData.length
#guard !schemaDense chainWithData
#guard (schemaClosedEdges chainWithData).2
#guard Graph.mem ⟨.iri iI, rdfType, .iri (iriW "http://e.org/D")⟩
         (closureFixDispatch chainWithData)

/-! ### The reflective graph is where the fast path must NOT be trusted

`witnessReflective` fails the side condition, and the injected schema
edge is present in the dispatcher's answer either way — through the
fallback, not through the fast path. -/

#guard Graph.mem (sub cA cB) (closureFix witnessReflective)
#guard Graph.mem (sub cA cB) (closureFixDispatch witnessReflective)

/-! ### The density guard fires on an already-closed hierarchy -/

#guard schemaDense (List.range 40 |>.flatMap (fun i =>
  (List.range 40).map (fun j =>
    sub (iriW s!"http://e.org/c{i}") (iriW s!"http://e.org/c{j}"))))

end Checks

end L4Factoidal.RDFS
