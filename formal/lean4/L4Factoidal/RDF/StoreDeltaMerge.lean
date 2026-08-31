/-
L4Factoidal.RDF.StoreDeltaMerge — merge-on-read over a delta log.

Port of `formal/fstar/RDF.Store.Columnar.DeltaMerge.fst` (934 lines).

The COTTAS base file is immutable. A SPARQL UPDATE appends entries to a
delta log beside it (`Storage.DeltaLog` gives those entries their bytes
and their framing), and a later compaction folds the log into a fresh
base. Between those two events every read has to answer from base plus
log. This module is that arithmetic, and nothing in it does I/O: it
consumes an already-replayed list of batches and already-decoded base
results.

## One graph at a time

`DeltaResolved` is ONE graph's diff, and `foldDeltaBatches` takes the
graph key. That is forced by the shape of the overlay it feeds: the
overlay takes exactly one read seam — one graph's — and one resolved
delta, with no graph argument of its own. The wiring layer calls the
fold once per graph the log or the base mentions.

## CLEAR and DROP are not cancellations

A CLEAR after some ADDs must hide the BASE's own rows too, not merely
undo the ADDs recorded since. So `DeltaResolved` carries `cleared`,
which the design sketch did not have: it means "ignore the base
entirely for this graph, from here on". CREATE has no effect on any
triple set — it is existence bookkeeping — so the fold treats it as
inert, and `deltaBatchesNamedGraphs` is what lets a wiring layer still
make a CREATE-only graph resolvable.

## What is proved here

`mergeOnRead_matches_applyEntries`: reading base-plus-delta returns
exactly the triples that applying the SAME entries directly to the base
graph would have produced, for any bound. That is the bridge between
the durable path and direct in-memory application, and it is proved for
the whole vocabulary a delta entry can express — INSERT DATA, DELETE
DATA, CLEAR and DROP on one graph, in sequence.

The residual is the same one the F\* module records: a translator from
a general `UpdateOp` list to delta entries would also have to cover
DELETE/INSERT WHERE, COPY/MOVE/ADD between graphs and CLEAR ALL's
multi-graph fan-out. That needs WHERE-clause evaluation against the
composed store, which is not delta-log logic. The three Graph Store
Protocol verbs at the bottom of this file DO translate completely, and
they are the part that has no residual.
-/
import L4Factoidal.RDF.StoreCapabilities

namespace L4Factoidal.RDF

open L4Factoidal.SPARQL (PatternBound boundMatches tripleMatchesBound
  mem_tripleMatchesBound)
open L4Factoidal.Storage (DeltaEntry DeltaBatch filterBatchesSinceEpoch
  splitBatchesSinceEpoch? splitBatchesSinceEpoch?_sound)

/-! ## One graph's resolved diff -/

/-- `added` and `removed` are SETS: both are built with `Graph.add`, so
neither carries a duplicate. -/
structure DeltaResolved where
  /-- A CLEAR or DROP fired for this graph in this log. -/
  cleared : Bool
  /-- Net additions since the last clear. -/
  added : Graph
  /-- Net tombstones since the last clear. -/
  removed : Graph
  deriving Repr, DecidableEq, Inhabited

def deltaResolvedEmpty : DeltaResolved :=
  { cleared := false, added := [], removed := [] }

def deltaResolvedCleared : DeltaResolved :=
  { cleared := true, added := [], removed := [] }

/-- The case the overlay must reproduce the wrapped store's behaviour
exactly: an empty delta costs nothing, by a short circuit rather than
by an optimisation layered on top. -/
def deltaResolvedIsEmpty (dr : DeltaResolved) : Bool :=
  !dr.cleared && dr.added.isEmpty && dr.removed.isEmpty

/-! ## Folding a log into a diff, for one graph, in commit order

A delta log is append-only and is replayed front to back, so list order
IS commit order. -/

/-- Apply one entry. An entry that targets a different graph leaves the
diff untouched; `none` is the default graph, matching the entry type's
own convention. -/
def applyEntryToDelta (graphKey : Option Iri) (dr : DeltaResolved) (e : DeltaEntry) :
    DeltaResolved :=
  match e with
  | .add t g =>
      if g == graphKey then
        { dr with removed := Graph.remove t dr.removed, added := dr.added.add t }
      else dr
  | .remove t g =>
      if g == graphKey then
        { dr with added := Graph.remove t dr.added, removed := dr.removed.add t }
      else dr
  | .clear g => if g == graphKey then deltaResolvedCleared else dr
  | .drop g  => if some g == graphKey then deltaResolvedCleared else dr
  | .create _ => dr        -- existence bookkeeping only, no triple-set effect

def foldEntriesForGraph (graphKey : Option Iri) :
    List DeltaEntry → DeltaResolved → DeltaResolved
  | [], acc => acc
  | e :: rest, acc => foldEntriesForGraph graphKey rest (applyEntryToDelta graphKey acc e)

/-- The whole-log fold for one graph. Concatenating the batches'
operation lists preserves commit order, because the batches are already
in it. -/
def foldDeltaBatches (batches : List DeltaBatch) (graphKey : Option Iri) : DeltaResolved :=
  foldEntriesForGraph graphKey (batches.flatMap (·.ops)) deltaResolvedEmpty

/-! ## Which named graphs does this log mention?

A CREATE or an ADD against a brand-new named graph must leave that
graph resolvable — queryable, answering empty — even though the base
store has no rows for it. The wiring layer needs the list of names to
give each one a slot. -/

def entryGraphMentions (e : DeltaEntry) : List Iri :=
  match e with
  | .add _ g | .remove _ g | .clear g => match g with | none => [] | some gi => [gi]
  | .drop g | .create g => [g]

def dedupIri (xs : List Iri) : List Iri :=
  xs.foldl (fun seen x => if seen.contains x then seen else seen ++ [x]) []

/-- Every distinct named-graph IRI mentioned anywhere in the log, in
first-seen order. The default graph is absent, since it has no IRI. -/
def deltaBatchesNamedGraphs (batches : List DeltaBatch) : List Iri :=
  dedupIri (batches.flatMap (fun b => b.ops.flatMap entryGraphMentions))

/-! ## The read-time composition

`baseResults` is whatever the base backend already returned for the
SAME bound this call receives. Nothing here decides how the base is
read. -/

/-- The base rows that survive the delta: none at all once a CLEAR has
fired, otherwise those with no tombstone. -/
def filterTombstoned (baseResults : Graph) (dr : DeltaResolved) : Graph :=
  if dr.cleared then []
  else baseResults.filter (fun t => !Graph.mem t dr.removed)

def mergeOnRead (baseResults : Graph) (dr : DeltaResolved) (b : PatternBound) : Graph :=
  Graph.union (filterTombstoned baseResults dr) (tripleMatchesBound b dr.added)

/-- Cheap: proportional to the delta, never touching the base results.
This is the additive term the overlay's estimate uses. -/
def deltaMatchingCount (dr : DeltaResolved) (b : PatternBound) : Nat :=
  (tripleMatchesBound b dr.added).length

/-- Proportional to the base results. The overlay calls it only when the
delta is non-empty; an empty delta short-circuits first, which is what
makes "an empty delta costs nothing" exact rather than approximate. -/
def tombstonedCount (dr : DeltaResolved) (baseResults : Graph) : Nat :=
  if dr.cleared then baseResults.length
  else (baseResults.filter (fun t => Graph.mem t dr.removed)).length

/-- Conservative predicate presence: never a false negative. A predicate
tombstoned down to zero rows can still report present, which is safe for
a planner short circuit and is the same direction the backends' own
presence probes already accept. -/
def deltaAddedHasPredicate (added : Graph) (pred : WfIri) : Bool :=
  added.any (fun t => t.p == pred)

/-! ## The reference model

What a durable-update-naive in-memory engine would do if it re-applied
the same entries as literal graph operations, with no base-plus-delta
split at all. The theorem below says the two agree. -/

def applyEntryRefStep (graphKey : Option Iri) (g : Graph) (e : DeltaEntry) : Graph :=
  match e with
  | .add t gr    => if gr == graphKey then g.add t else g
  | .remove t gr => if gr == graphKey then Graph.remove t g else g
  | .clear gr    => if gr == graphKey then [] else g
  | .drop gr     => if some gr == graphKey then [] else g
  | .create _    => g

def applyEntriesRef (graphKey : Option Iri) : Graph → List DeltaEntry → Graph
  | g, [] => g
  | g, e :: rest => applyEntriesRef graphKey (applyEntryRefStep graphKey g e) rest

/-! ## The correctness bridge

The invariant carried through the induction: after applying the SAME
entries to a reference graph and to a (base, diff) pair that started
equal, the reference graph holds a triple exactly when base-composed-
with-diff does. -/

/-- Membership in the composed view: base rows that survive the delta,
plus the delta's own additions.

Written as one boolean expression rather than a branch on `cleared`,
because a branch whose CONDITION mentions the record makes the rewrite
motive depend on the record, and every step of the induction below
rewrites the record. Same truth table either way: with `cleared` set the
first conjunct vanishes and only the additions remain. -/
def composedMem (gBase : Graph) (dr : DeltaResolved) (t : Triple) : Bool :=
  (!dr.cleared && Graph.mem t gBase && !Graph.mem t dr.removed) || Graph.mem t dr.added

def StateAgrees (gRef gBase : Graph) (dr : DeltaResolved) : Prop :=
  ∀ t : Triple, Graph.mem t gRef = composedMem gBase dr t

theorem stateAgrees_init (gBase : Graph) :
    StateAgrees gBase gBase deltaResolvedEmpty := by
  intro t
  simp [composedMem, deltaResolvedEmpty, Graph.mem]

/-- The tombstone filter's predicate respects the engine equality, so
`mem_filter_congr` applies to it. -/
theorem tombstone_congr (dr : DeltaResolved) (a b : Triple) (h : Triple.eqb a b = true) :
    (!Graph.mem a dr.removed) = (!Graph.mem b dr.removed) := by
  cases ha : Graph.mem a dr.removed with
  | true => simp [ha, graphMem_of_graphMem_eqb ha h]
  | false =>
      cases hb : Graph.mem b dr.removed with
      | true =>
          exact absurd
            (graphMem_of_graphMem_eqb hb (by rw [Triple.eqb_symm]; exact h))
            (by rw [ha]; simp)
      | false => simp

theorem mem_filterTombstoned (baseResults : Graph) (dr : DeltaResolved) (t : Triple) :
    Graph.mem t (filterTombstoned baseResults dr) =
      (!dr.cleared && Graph.mem t baseResults && !Graph.mem t dr.removed) := by
  unfold filterTombstoned
  cases hc : dr.cleared with
  | true => simp [Graph.mem]
  | false => simpa using mem_filter_congr (tombstone_congr dr) t baseResults

/-- One entry preserves the invariant. Each of the five constructors
either leaves both sides untouched, or moves both through the SAME add,
remove or clear. -/
theorem stateAgrees_step (graphKey : Option Iri) (gRef gBase : Graph)
    (dr : DeltaResolved) (e : DeltaEntry) (h : StateAgrees gRef gBase dr) :
    StateAgrees (applyEntryRefStep graphKey gRef e) gBase
      (applyEntryToDelta graphKey dr e) := by
  intro t
  have ht := h t
  cases e with
  | add q g =>
      simp only [applyEntryRefStep, applyEntryToDelta]
      by_cases hg : (g == graphKey) = true
      · rw [if_pos hg, if_pos hg]
        simp only [composedMem, mem_graph_add, mem_graph_remove, ht] at *
        cases dr.cleared <;> cases Triple.eqb q t <;>
          cases Graph.mem t gBase <;> cases Graph.mem t dr.removed <;>
          cases Graph.mem t dr.added <;> rfl
      · rw [if_neg hg, if_neg hg]; exact ht
  | remove q g =>
      simp only [applyEntryRefStep, applyEntryToDelta]
      by_cases hg : (g == graphKey) = true
      · rw [if_pos hg, if_pos hg]
        simp only [composedMem, mem_graph_add, mem_graph_remove, ht] at *
        cases dr.cleared <;> cases Triple.eqb q t <;>
          cases Graph.mem t gBase <;> cases Graph.mem t dr.removed <;>
          cases Graph.mem t dr.added <;> rfl
      · rw [if_neg hg, if_neg hg]; exact ht
  | clear g =>
      simp only [applyEntryRefStep, applyEntryToDelta]
      by_cases hg : (g == graphKey) = true
      · rw [if_pos hg, if_pos hg]; simp [composedMem, deltaResolvedCleared, Graph.mem]
      · rw [if_neg hg, if_neg hg]; exact ht
  | drop g =>
      simp only [applyEntryRefStep, applyEntryToDelta]
      by_cases hg : (some g == graphKey) = true
      · rw [if_pos hg, if_pos hg]; simp [composedMem, deltaResolvedCleared, Graph.mem]
      · rw [if_neg hg, if_neg hg]; exact ht
  | create g =>
      simp only [applyEntryRefStep, applyEntryToDelta]
      exact ht

theorem applyEntries_stateAgrees (graphKey : Option Iri) (gBase : Graph) :
    ∀ (entries : List DeltaEntry) (gRef : Graph) (dr : DeltaResolved),
      StateAgrees gRef gBase dr →
      StateAgrees (applyEntriesRef graphKey gRef entries) gBase
        (foldEntriesForGraph graphKey entries dr)
  | [], _, _, h => h
  | e :: rest, gRef, dr, h => by
      unfold applyEntriesRef foldEntriesForGraph
      exact applyEntries_stateAgrees graphKey gBase rest _ _ (stateAgrees_step _ _ _ _ e h)

/-- **The bridge.** Querying the reference graph — the entries applied
directly — agrees triple for triple with `mergeOnRead` over the fold of
the same entries against the same base, for any bound.

Stated as membership rather than list equality, which is the right
statement: both sides are graphs, and a graph is a set of triples. The
two lists can differ in ORDER, because `mergeOnRead` puts the delta's
additions after the surviving base rows while the reference model keeps
each triple where it first landed. SPARQL gives an unordered basic
graph pattern no order guarantee, so this is the property the evaluator
relies on. -/
theorem mergeOnRead_matches_applyEntries (graphKey : Option Iri) (gBase : Graph)
    (entries : List DeltaEntry) (b : PatternBound) (t : Triple) :
    Graph.mem t (tripleMatchesBound b (applyEntriesRef graphKey gBase entries)) =
    Graph.mem t (mergeOnRead (tripleMatchesBound b gBase)
                   (foldEntriesForGraph graphKey entries deltaResolvedEmpty) b) := by
  have hag := applyEntries_stateAgrees graphKey gBase entries gBase deltaResolvedEmpty
                (stateAgrees_init gBase) t
  unfold mergeOnRead
  rw [mem_tripleMatchesBound, mem_graph_union, mem_filterTombstoned,
      mem_tripleMatchesBound, mem_tripleMatchesBound, hag]
  simp only [composedMem] at *
  cases (foldEntriesForGraph graphKey entries deltaResolvedEmpty).cleared <;>
    cases boundMatches b t <;>
    cases Graph.mem t gBase <;>
    cases Graph.mem t (foldEntriesForGraph graphKey entries deltaResolvedEmpty).removed <;>
    cases Graph.mem t (foldEntriesForGraph graphKey entries deltaResolvedEmpty).added <;>
    rfl

/-- Applying an older log prefix to a base and then a newer suffix is the
same reference history as applying their concatenation. This is the algebraic
form a compactor needs before it may discard the prefix from replay. -/
theorem applyEntriesRef_append (graphKey : Option Iri) (gBase : Graph)
    (older newer : List DeltaEntry) :
    applyEntriesRef graphKey gBase (older ++ newer) =
      applyEntriesRef graphKey (applyEntriesRef graphKey gBase older) newer := by
  induction older generalizing gBase with
  | nil => rfl
  | cons entry older ih =>
    simp only [List.cons_append, applyEntriesRef]
    exact ih (applyEntryRefStep graphKey gBase entry)

/-- **Compaction bridge.** If `older` has been folded into a fresh immutable
base, replaying only `newer` through `mergeOnRead` has the same membership
answer as applying the full pre-compaction history. Epoch filtering supplies
that `newer` suffix at the durable-store boundary. -/
theorem mergeOnRead_after_compaction (graphKey : Option Iri) (gBase : Graph)
    (older newer : List DeltaEntry) (b : PatternBound) (t : Triple) :
    Graph.mem t (tripleMatchesBound b (applyEntriesRef graphKey gBase (older ++ newer))) =
    Graph.mem t (mergeOnRead
      (tripleMatchesBound b (applyEntriesRef graphKey gBase older))
      (foldEntriesForGraph graphKey newer deltaResolvedEmpty) b) := by
  rw [applyEntriesRef_append]
  exact mergeOnRead_matches_applyEntries graphKey
    (applyEntriesRef graphKey gBase older) newer b t

/-- **Epoch-filtered compaction bridge.** A durable reader may discard exactly
    those committed batches that were folded into its immutable base. The two
    hypotheses make the storage boundary explicit: `hHistory` says which
    prefix was folded, and `hFiltered` says the CEP1 threshold leaves exactly
    the later batches. Under those admitted facts, replaying the filtered DLOG
    cannot double-apply the compacted prefix and has the same membership
    result as the complete history. -/
theorem mergeOnRead_after_epoch_compaction (baseEpoch : Nat)
    (graphKey : Option Iri) (gBase : Graph) (batches newer : List DeltaBatch)
    (older : List DeltaEntry)
    (hHistory : batches.flatMap (·.ops) = older ++ newer.flatMap (·.ops))
    (hFiltered : filterBatchesSinceEpoch (some baseEpoch) batches = newer)
    (b : PatternBound) (t : Triple) :
    Graph.mem t (tripleMatchesBound b
      (applyEntriesRef graphKey gBase (batches.flatMap (·.ops)))) =
    Graph.mem t (mergeOnRead
      (tripleMatchesBound b (applyEntriesRef graphKey gBase older))
      (foldDeltaBatches (filterBatchesSinceEpoch (some baseEpoch) batches) graphKey) b) := by
  rw [hHistory, hFiltered]
  exact mergeOnRead_after_compaction graphKey gBase older (newer.flatMap (·.ops)) b t

/-- The directly usable no-double-replay form. A successful CEP1 partition
    supplies both facts required by `mergeOnRead_after_epoch_compaction`, so
    callers do not need to assume a separate history split or filter result. -/
theorem mergeOnRead_after_epoch_partition (baseEpoch : Nat)
    (graphKey : Option Iri) (gBase : Graph) (batches older newer : List DeltaBatch)
    (hPartition : splitBatchesSinceEpoch? baseEpoch batches = some (older, newer))
    (b : PatternBound) (t : Triple) :
    Graph.mem t (tripleMatchesBound b
      (applyEntriesRef graphKey gBase (batches.flatMap (·.ops)))) =
    Graph.mem t (mergeOnRead
      (tripleMatchesBound b (applyEntriesRef graphKey gBase (older.flatMap (·.ops))))
      (foldDeltaBatches newer graphKey) b) := by
  obtain ⟨hHistory, hFilter⟩ :=
    splitBatchesSinceEpoch?_sound baseEpoch batches older newer hPartition
  have hOps := congrArg (List.flatMap fun batch => batch.ops) hHistory
  simp only [List.flatMap_append] at hOps
  simpa only [hFilter] using
    (mergeOnRead_after_epoch_compaction baseEpoch graphKey gBase batches newer
      (older.flatMap (·.ops)) hOps hFilter b t)

/-! ## Graph Store Protocol write verbs

Unlike a general UPDATE request, all three of these translate
completely — there is no case that fails, so no `Option` return. Each is
a whole-graph operation against one already-resolved target, with no
WHERE clause, no multi-graph fan-out and no blank-node freshening. -/

/-- PUT replaces the graph. That is a CLEAR followed by an ADD of every
triple: the fold processes entries in order and a CLEAR resets the
addition set, so the ADDs that follow land in a genuinely emptied
accumulator. -/
def gspPutToDeltaEntries (graphKey : Option Iri) (g : Graph) : List DeltaEntry :=
  .clear graphKey :: g.map (fun t => .add t graphKey)

/-- POST merges. No CLEAR — `mergeOnRead`'s union with the base already
gives set semantics, and `Graph.add`'s deduplication makes a re-added
triple a no-op. -/
def gspPostToDeltaEntries (graphKey : Option Iri) (g : Graph) : List DeltaEntry :=
  g.map (fun t => .add t graphKey)

/-- DELETE empties the graph: one CLEAR. -/
def gspDeleteToDeltaEntries (graphKey : Option Iri) : List DeltaEntry :=
  [.clear graphKey]

/-! ## Build-time checks -/

section Checks

private def iriW (s : String) : WfIri :=
  if h : isIri s then ⟨s, h⟩ else ⟨"http://e.org/", by decide⟩

private def t1 : Triple := ⟨.iri (iriW "http://e.org/a"), iriW "http://e.org/p",
                            .iri (iriW "http://e.org/1")⟩
private def t2 : Triple := ⟨.iri (iriW "http://e.org/b"), iriW "http://e.org/p",
                            .iri (iriW "http://e.org/2")⟩
private def t3 : Triple := ⟨.iri (iriW "http://e.org/c"), iriW "http://e.org/q",
                            .iri (iriW "http://e.org/3")⟩

private def g1 : Iri := "http://e.org/g1"

private def fold (es : List DeltaEntry) (k : Option Iri) : DeltaResolved :=
  foldEntriesForGraph k es deltaResolvedEmpty

/-! ### An entry for another graph does not touch this graph's diff -/

#guard deltaResolvedIsEmpty (fold [.add t1 (some g1)] none)
#guard !deltaResolvedIsEmpty (fold [.add t1 none] none)

/-! ### ADD then REMOVE of the same triple leaves a tombstone, not
nothing: the base may hold that triple, and the tombstone is what hides
it. -/

#guard (fold [.add t1 none, .remove t1 none] none).added == []
#guard (fold [.add t1 none, .remove t1 none] none).removed == [t1]

/-! ### REMOVE then ADD cancels the tombstone -/

#guard (fold [.remove t1 none, .add t1 none] none).added == [t1]
#guard (fold [.remove t1 none, .add t1 none] none).removed == []

/-! ### CLEAR hides the BASE too, which is the whole reason for the flag -/

#guard (fold [.add t1 none, .clear none] none).cleared
#guard (fold [.add t1 none, .clear none] none).added == []
#guard mergeOnRead [t2] (fold [.clear none] none) {} == []

/-! ### DROP of a named graph clears that graph and no other -/

#guard (fold [.drop g1] (some g1)).cleared
#guard !(fold [.drop g1] none).cleared

/-! ### CREATE moves no triple -/

#guard deltaResolvedIsEmpty (fold [.create g1] (some g1))
#guard deltaBatchesNamedGraphs [⟨0, 0, [.create g1]⟩] == [g1]
#guard deltaBatchesNamedGraphs [⟨0, 0, [.add t1 none, .create g1, .drop g1]⟩] == [g1]

/-! ### merge-on-read: the base survives, the tombstone hides, the
addition appears -/

#guard mergeOnRead [t1, t2] (fold [.remove t1 none] none) {} == [t2]
#guard mergeOnRead [t1] (fold [.add t2 none] none) {} == [t1, t2]
#guard mergeOnRead [t1] (fold [.add t1 none] none) {} == [t1]
#guard mergeOnRead [t1] deltaResolvedEmpty {} == [t1]

/-! ### The bound applies to the delta's additions as well as the base -/

#guard mergeOnRead [] (fold [.add t1 none, .add t3 none] none)
         { p := some (iriW "http://e.org/p") } == [t1]
#guard deltaMatchingCount (fold [.add t1 none, .add t3 none] none)
         { p := some (iriW "http://e.org/q") } == 1

/-! ### Presence is conservative in the safe direction: a tombstoned
predicate can still report present through the base, and the delta's own
additions are checked. -/

#guard deltaAddedHasPredicate (fold [.add t3 none] none).added (iriW "http://e.org/q")
#guard !deltaAddedHasPredicate (fold [.add t3 none] none).added (iriW "http://e.org/p")

/-! ### The GSP verbs

PUT replaces: the base row `t1` is gone and only `t2` remains. POST
merges: both survive. DELETE empties. -/

private def gspFold (es : List DeltaEntry) : DeltaResolved := fold es none

#guard mergeOnRead [t1] (gspFold (gspPutToDeltaEntries none [t2])) {} == [t2]
#guard mergeOnRead [t1] (gspFold (gspPostToDeltaEntries none [t2])) {} == [t1, t2]
#guard mergeOnRead [t1] (gspFold (gspDeleteToDeltaEntries none)) {} == []

/-! ### The bridge, checked by evaluation as well as proved

The theorem says the two sides hold the same triples. These check that
on concrete inputs, which also pins that the theorem is not vacuous —
each side really does produce rows. -/

private def bridgeAgrees (es : List DeltaEntry) (base : Graph) (b : PatternBound) : Bool :=
  let lhs := tripleMatchesBound b (applyEntriesRef none base es)
  let rhs := mergeOnRead (tripleMatchesBound b base) (fold es none) b
  lhs.all (fun t => Graph.mem t rhs) && rhs.all (fun t => Graph.mem t lhs)

#guard bridgeAgrees [.add t2 none] [t1] {}
#guard bridgeAgrees [.remove t1 none] [t1, t2] {}
#guard bridgeAgrees [.clear none, .add t3 none] [t1, t2] {}
#guard bridgeAgrees [.add t1 none, .remove t1 none, .add t1 none] [t2] {}
#guard bridgeAgrees [.add t3 none] [t1] { p := some (iriW "http://e.org/p") }
#guard bridgeAgrees [.add t1 (some g1)] [t2] {}

/-! Not vacuous: the two sides above are non-empty. -/

#guard (mergeOnRead (tripleMatchesBound {} [t1]) (fold [.add t2 none] none) {}).length == 2

end Checks

end L4Factoidal.RDF
