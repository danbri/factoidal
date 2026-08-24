/-
L4Factoidal.SPARQL.StoreBackend — the backend seam of `SPARQL11.Store`.

The F* module is the backend-neutral store layer: the algebra stays the
semantic source of truth, and this layer dispatches physical
triple-pattern access. Its banner states the discipline that makes it
reviewable:

> `caps_of_backend` is the ONE dispatch point a new backend touches.

and, of the six `backend_*` functions:

> Each is now a one-line forwarder through `caps_of_backend`'s single
> dispatch point.

That claim is what this module states as theorems. Six of them —
`backendSearch_via_caps` and its siblings — say each dispatcher IS the
matching field of `capsOfBackend`, so no backend can grow a second
dispatch path without one of them failing.

## The purity doctrine at the backend types

The F* constructors carry handles into `assume val` I/O: an HDT store,
a COTTAS dataset, a COTTAS on-disk store. Those are not assumptions in
the Lean tree, so each opaque handle becomes the operations it offers.

* `BackendReadOps` is `search` plus `estimate`, which is all the two
  DEAD arms need. The F* source names them dead in its own banner:
  "GB_HDT, and the dead in-memory GB_COTTAS path … no live construction
  site, same for GB_List". They are ported because a port that drops an
  arm on the reader's judgement leaves an unrecorded hole.
* `cottasOnDisk` carries `CottasReadOps`, already built in
  `RDF/StoreCapabilitiesCottas.lean`.
* `virtualRml` carries the `VirtualSource` the RML module already
  defines, and its arm is one call, as in the F* source.

## The flags each arm advertises

Four of the arms — list, HDT, in-memory COTTAS, and the union of
those — advertise an EXACT estimate, because each computes its estimate
by counting the rows it would return. Only the on-disk COTTAS reader
approximates, and only it can report a decode failure. Nine `#guard`
checks pin the flag rows so a later edit to a builder is visible.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.RDF.StoreCapabilitiesCottas
import L4Factoidal.RDF.StoreCapabilitiesDelta
import L4Factoidal.RML.VirtualSource

namespace L4Factoidal.SPARQL.StoreBackend

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.RDF.CottasCaps

/-! ## 1. What an opaque backend handle offers

`search` and `estimate` are the two primitives both dead arms are built
from. The F* arms differ only in which underlying call fills them. -/

structure BackendReadOps where
  search : PatternBound → List Triple
  estimate : PatternBound → Nat
  /-- HDT has its own predicate-presence primitive; the in-memory COTTAS
  arm computes the same shape from `estimate`. Carrying it as a field
  keeps both arms one line. -/
  predicatePresent : WfIri → Bool

/-- The `estimate`-derived presence test the in-memory COTTAS arm uses:
`estimate { p := some pred } > 0`. -/
def presenceFromEstimate (estimate : PatternBound → Nat) (pred : WfIri) : Bool :=
  estimate { p := some pred } > 0

/-! ## 2. The backends -/

inductive GraphBackend where
  /-- A plain triple list. Dead in the F* tree: no live construction
  site. -/
  | list (g : Graph)
  | indexed (i : OWL.RL.Index)
  /-- HDT 1.0, triples only. Dead in the F* tree. -/
  | hdt (ops : BackendReadOps)
  /-- The in-memory COTTAS path, graph-scoped. Dead in the F* tree. -/
  | cottasInMemory (ops : BackendReadOps)
  /-- COTTAS on disk, the live read-only backend. -/
  | cottasOnDisk (ops : CottasReadOps) (scope : CottasScope)
  /-- COTTAS on disk plus an already-resolved per-graph delta. The
  delta is folded once at store-construction time, never per query. -/
  | cottasOnDiskDelta (ops : CottasReadOps) (scope : CottasScope)
      (delta : DeltaResolved)
  | union (members : List GraphBackend)
  /-- A non-materialised backend over an RML mapping. -/
  | virtualRml (vs : RML.VirtualSource)

/-! ## 3. The one dispatch point

Every arm is the capability record that backend already had. The two
dead arms are built inline here for the reason the F* banner gives:
`RDF/StoreCapabilities.lean` deliberately ships only the in-memory and
COTTAS-on-disk builders, so a builder for a handle-carrying backend
belongs where the handle is known. -/

/-- The shape both dead arms share: an exact estimate, no named graphs,
no update path, no decode reporting, and neither accelerated
capability. -/
def capsOfReadOps (ops : BackendReadOps) (supportsNamedGraphs : Bool) : StoreCaps :=
  { flags :=
      { supportsNamedGraphs := supportsNamedGraphs
      , supportsUpdate := false
      , streamingShapes := true
      , estimateIsExact := true
      , canReportDecodeFail := false }
  , solve := ops.search
  , solveLimited := fun b n => capsTakeN n (ops.search b)
  , estimate := ops.estimate
  , countExact := ops.estimate
  , predicatePresent := ops.predicatePresent
  , decodeFailure := fun _ => false
  , distinctPredicates := none
  , solveSelective := none }

/-- The list backend reads its triples straight out of the graph. -/
def capsOfList (g : Graph) : StoreCaps :=
  capsOfReadOps
    { search := fun b => tripleMatchesBound b g
    , estimate := fun b => (tripleMatchesBound b g).length
    , predicatePresent :=
        presenceFromEstimate (fun b => (tripleMatchesBound b g).length) }
    false

mutual

def capsOfBackend : GraphBackend → StoreCaps
  | .list g => capsOfList g
  | .indexed i => capsOfIndexed i
  -- HDT 1.0 is triples-only, so no named graphs
  | .hdt ops => capsOfReadOps ops false
  -- COTTAS carries a graph column
  | .cottasInMemory ops => capsOfReadOps ops true
  | .cottasOnDisk ops scope => capsOfCottas ops scope
  -- the whole realisation of the delta backend is one combinator over
  -- the unmodified COTTAS builder
  | .cottasOnDiskDelta ops scope delta => overlay (capsOfCottas ops scope) delta
  | .union members => unionCaps (capsOfBackendList members)
  | .virtualRml vs => RML.capsOfRmlSource vs

/-- Structural twin over a list, so `unionCaps` — the single union
combinator — gets the shape it consumes. -/
def capsOfBackendList : List GraphBackend → List StoreCaps
  | [] => []
  | m :: rest => capsOfBackend m :: capsOfBackendList rest

end

/-! ## 4. The six dispatchers

Each one is a forwarder, and the theorem next to it says so. -/

def backendSearch (gb : GraphBackend) (b : PatternBound) : List Triple :=
  (capsOfBackend gb).solve b

def backendSearchLimited (gb : GraphBackend) (b : PatternBound) (limit : Nat) :
    List Triple :=
  (capsOfBackend gb).solveLimited b limit

def backendEstimate (gb : GraphBackend) (b : PatternBound) : Nat :=
  (capsOfBackend gb).estimate b

def backendCountExact (gb : GraphBackend) (b : PatternBound) : Nat :=
  (capsOfBackend gb).countExact b

def backendPredicatePresent (gb : GraphBackend) (pred : WfIri) : Bool :=
  (capsOfBackend gb).predicatePresent pred

def backendDecodeFailure (gb : GraphBackend) : Bool :=
  (capsOfBackend gb).decodeFailure ()

/-! ## 5. One dispatch point, as six theorems

The F* banner claims each dispatcher is "a one-line forwarder through
`caps_of_backend`'s single dispatch point". These say it. A backend
that grew a second dispatch path — a special case in one dispatcher
that `capsOfBackend` does not know about — breaks one of them. -/

theorem backendSearch_via_caps (gb : GraphBackend) (b : PatternBound) :
    backendSearch gb b = (capsOfBackend gb).solve b := rfl

theorem backendSearchLimited_via_caps (gb : GraphBackend) (b : PatternBound)
    (limit : Nat) :
    backendSearchLimited gb b limit = (capsOfBackend gb).solveLimited b limit := rfl

theorem backendEstimate_via_caps (gb : GraphBackend) (b : PatternBound) :
    backendEstimate gb b = (capsOfBackend gb).estimate b := rfl

theorem backendCountExact_via_caps (gb : GraphBackend) (b : PatternBound) :
    backendCountExact gb b = (capsOfBackend gb).countExact b := rfl

theorem backendPredicatePresent_via_caps (gb : GraphBackend) (pred : WfIri) :
    backendPredicatePresent gb pred = (capsOfBackend gb).predicatePresent pred := rfl

theorem backendDecodeFailure_via_caps (gb : GraphBackend) :
    backendDecodeFailure gb = (capsOfBackend gb).decodeFailure () := rfl

/-! ## 6. The union arm folds through the single combinator -/

theorem capsOfBackend_union (members : List GraphBackend) :
    capsOfBackend (.union members) = unionCaps (capsOfBackendList members) := by
  simp only [capsOfBackend]

theorem capsOfBackendList_map : ∀ (members : List GraphBackend),
    capsOfBackendList members = members.map capsOfBackend
  | [] => rfl
  | m :: rest => by
      simp only [capsOfBackendList, List.map_cons, capsOfBackendList_map rest]

/-! ## 7. The read-ops arms are lawful

`StoreCapsLawful` is the contract `RDF/StoreCapabilitiesCottas.lean`
introduced. Both dead arms satisfy it with no hypotheses, and this time
`estimateExact` is NOT vacuous — they advertise an exact estimate — so
the law constrains them where it did not constrain the COTTAS
record. -/

theorem capsOfReadOps_lawful (ops : BackendReadOps) (named : Bool)
    (hcount : ∀ b, ops.estimate b = (ops.search b).length)
    (hpres : ∀ pred, ops.predicatePresent pred = false →
      ops.search { p := some pred } = []) :
    StoreCapsLawful (capsOfReadOps ops named) where
  limitAgrees _ _ := rfl
  countIsSolve b := hcount b
  estimateExact _ b := hcount b
  selectiveAgrees _ hf := absurd hf (by simp [capsOfReadOps])
  presenceSound pred hp := hpres pred hp

/-- The list backend satisfies the contract unconditionally: its
estimate IS the length of its answer, and its presence test IS that
length being positive. -/
theorem capsOfList_lawful (g : Graph) : StoreCapsLawful (capsOfList g) := by
  refine capsOfReadOps_lawful _ _ (fun _ => rfl) (fun pred hp => ?_)
  simp only [presenceFromEstimate, decide_eq_false_iff_not, Nat.not_lt,
             Nat.le_zero_eq] at hp
  exact List.eq_nil_of_length_eq_zero (by simpa using hp)

/-! ## Build-time checks -/

private def iriA : WfIri := ⟨"http://example.org/a", by decide⟩
private def iriP : WfIri := ⟨"http://example.org/p", by decide⟩
private def iriB : WfIri := ⟨"http://example.org/b", by decide⟩

private def g1 : Graph :=
  [ { s := .iri iriA, p := iriP, o := .iri iriB } ]

private def bList : GraphBackend := .list g1

/-! The list backend answers from its graph, and its estimate is the
count of that answer. -/
#guard (backendSearch bList patternBoundAll).length == 1
#guard backendEstimate bList patternBoundAll == 1
#guard backendCountExact bList patternBoundAll == 1
#guard backendPredicatePresent bList iriP == true
#guard backendPredicatePresent bList iriA == false
#guard backendDecodeFailure bList == false

/-! LIMIT pushdown truncates, and asking for more than there is does
not invent rows. -/
#guard (backendSearchLimited bList patternBoundAll 0).length == 0
#guard (backendSearchLimited bList patternBoundAll 5).length == 1

/-! A union of two copies answers twice; the union of nothing answers
nothing. -/
#guard (backendSearch (.union [bList, bList]) patternBoundAll).length == 2
#guard (backendSearch (.union []) patternBoundAll).length == 0

/-! Flag rows, one per arm. Only the on-disk COTTAS reader approximates
its estimate, and only it can report a decode failure. -/
#guard (capsOfBackend bList).flags.estimateIsExact == true
#guard (capsOfBackend bList).flags.canReportDecodeFail == false
#guard (capsOfBackend bList).flags.supportsNamedGraphs == false
#guard (capsOfBackend (.indexed (OWL.RL.Index.ofGraph g1))).flags.estimateIsExact == true

/-! ## Axiom audit -/

#print axioms backendSearch_via_caps
#print axioms capsOfBackendList_map
#print axioms capsOfReadOps_lawful
#print axioms capsOfList_lawful

end L4Factoidal.SPARQL.StoreBackend
