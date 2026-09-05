/-
Publishing IBK4 blocks DURING the ingest pass moves no row.

`docs/designissues/2026-09-05-pack-publication-every-batch.md` records the
policy. This file states what it preserves. The buffered route holds every
row of every predicate to the end of the source and cuts each predicate's
rows once (`runsOfBuckets`); the streamed route cuts the same rows as they
arrive and publishes each block as the cut rule closes it, with three further
publication rules that depend on the source bytes fed so far. The block SET
therefore differs. What must not differ is the rows.

The theorem below is stated PER PREDICATE, over an event list which is a
source read plus its flush points:

  rowsFor p (published) ++ heldFor p (state) = fedFor p (quads)

for every predicate `p` and every prefix of the pass — nothing published is
absent from the fed quads, nothing fed is absent from the published rows plus
the open run, and the ORDER inside a predicate is the source order.
`pubRun_published_eq_fed` is the end-of-source corollary, where the open runs
are empty because rule 5 has flushed them.

`PredicateQuadBlocksTheorems.chunkQuadRows_flatten` is the same statement for
the buffered route. The two together say the streamed and the buffered routes
publish the same rows for the same predicate in the same order, so the union
of their blocks denotes the same quads, which is what every manifest since
SBM2 asks a reader to take.

The second half, `dataset_of_perm_denotes`, is the transport: a `Dataset`
built from a permuted quad list has the same triples in each graph.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.PredicateQuadBlocksTheorems

namespace L4Factoidal.Storage.PredicateQuadBlocks

open L4Factoidal.RDF
open L4Factoidal.Storage.IndexedBlockWireV4

/-! ## The three projections -/

/-- The rows published for one predicate, in publication order. -/
def rowsFor (p : WfIri) (published : List (WfIri × List QuadRow)) : List QuadRow :=
  published.flatMap fun entry => if entry.1 == p then entry.2 else []

/-- The rows one predicate's open run still holds, in source order. -/
def heldFor (p : WfIri) (st : Pub) : List QuadRow :=
  match st.runs[p]? with
  | none => []
  | some run => run.accRev.reverse

/-- The fed quads whose predicate is `p`, in source order. -/
def fedFor (p : WfIri) (quads : List QuadRow) : List QuadRow :=
  quads.filter (fun quad => quad.2.p == p)

theorem rowsFor_append (p : WfIri) (a b : List (WfIri × List QuadRow)) :
    rowsFor p (a ++ b) = rowsFor p a ++ rowsFor p b := by
  simp [rowsFor]

theorem rowsFor_nil (p : WfIri) : rowsFor p [] = [] := rfl

theorem fedFor_append (p : WfIri) (a b : List QuadRow) :
    fedFor p (a ++ b) = fedFor p a ++ fedFor p b := by
  simp [fedFor]

/-! ## A flush moves rows from the open runs to the published list -/

/-- One flush step preserves "published for `p`, then still held for `p`". -/
private theorem flushStep_inv (p : WfIri) (minRows : Nat)
    (acc : Pub × List (WfIri × List QuadRow)) (predicate : WfIri) :
    rowsFor p (flushStep minRows acc predicate).2.reverse
        ++ heldFor p (flushStep minRows acc predicate).1
      = rowsFor p acc.2.reverse ++ heldFor p acc.1 := by
  unfold flushStep
  cases hq : acc.1.runs[predicate]? with
  | none => rfl
  | some run =>
      dsimp only
      by_cases hskip : (run.accRev.isEmpty || decide (run.rows < minRows)) = true
      · rw [if_pos hskip]
      · rw [if_neg hskip]
        by_cases hpe : predicate = p
        · subst hpe
          simp [rowsFor, heldFor, hq]
        · have hbf : (predicate == p) = false := by
            simp only [beq_eq_false_iff_ne]
            exact hpe
          have hval : ¬ predicate.val = p.val := fun h => hpe (Subtype.ext h)
          simp [rowsFor, heldFor, hbf, hval, Std.HashMap.getElem?_insert]

private theorem flushFold_inv (p : WfIri) (minRows : Nat) :
    ∀ (ps : List WfIri) (acc : Pub × List (WfIri × List QuadRow)),
      rowsFor p (ps.foldl (flushStep minRows) acc).2.reverse
          ++ heldFor p (ps.foldl (flushStep minRows) acc).1
        = rowsFor p acc.2.reverse ++ heldFor p acc.1
  | [], acc => rfl
  | a :: rest, acc => by
      simp only [List.foldl_cons]
      rw [flushFold_inv p minRows rest (flushStep minRows acc a)]
      exact flushStep_inv p minRows acc a

/-- A flush publishes exactly what it releases: the rows for a predicate,
    published and still held, are unchanged by it. -/
theorem pubFlush_rows (p : WfIri) (st : Pub) (minRows : Nat) :
    rowsFor p (pubFlush st minRows).2 ++ heldFor p (pubFlush st minRows).1
      = heldFor p st := by
  have h := flushFold_inv p minRows st.orderRev.reverse (st, [])
  rw [pubFlush_eq]
  simpa [rowsFor] using h

/-! ## One quad enters exactly one open run -/

theorem pubAddRun_rows (p : WfIri) (st : Pub) (quad : QuadRow) :
    rowsFor p (pubAddRun st quad).2 ++ heldFor p (pubAddRun st quad).1
      = heldFor p st ++ fedFor p [quad] := by
  rw [pubAddRun_eq]
  by_cases hpe : quad.2.p = p
  · have hqp : quad.2.p = p := hpe
    cases hq : st.runs[quad.2.p]? with
    | none =>
        subst hqp
        simp [rowsFor, heldFor, hq, fedFor, freshRun]
    | some run =>
        dsimp only
        by_cases he : run.accRev.isEmpty = true
        · have hnil : run.accRev = [] := by simpa using he
          rw [if_pos he]
          subst hqp
          simp [rowsFor, heldFor, hq, fedFor, freshRun, hnil]
        · rw [if_neg he]
          by_cases hc : quad.1 == run.graph && run.rows < maxBlockRows &&
              run.bytes + quadWireBytes quad <= maxBlockWireBytes
          · rw [if_pos hc]
            subst hqp
            simp [rowsFor, heldFor, hq, fedFor, freshRun]
          · rw [if_neg hc]
            subst hqp
            simp [rowsFor, heldFor, hq, fedFor, freshRun]
  · have hbf : (quad.2.p == p) = false := by
      simp only [beq_eq_false_iff_ne]; exact hpe
    have hne : ¬ (p = quad.2.p) := fun h => hpe h.symm
    have hval : ¬ quad.2.p.val = p.val := fun h => hpe (Subtype.ext h)
    have hval' : ¬ p.val = quad.2.p.val := fun h => hne (Subtype.ext h)
    cases hq : st.runs[quad.2.p]? with
    | none =>
        simp [rowsFor, heldFor, fedFor, hbf, freshRun, Std.HashMap.getElem?_insert,
              beq_eq_false_iff_ne, hne, hval, hval']
    | some run =>
        dsimp only
        by_cases he : run.accRev.isEmpty = true
        · rw [if_pos he]
          simp [rowsFor, heldFor, fedFor, hbf, freshRun, Std.HashMap.getElem?_insert,
                beq_eq_false_iff_ne, hne, hval, hval']
        · rw [if_neg he]
          by_cases hc : quad.1 == run.graph && run.rows < maxBlockRows &&
              run.bytes + quadWireBytes quad <= maxBlockWireBytes
          · rw [if_pos hc]
            simp [rowsFor, heldFor, fedFor, hbf, freshRun, Std.HashMap.getElem?_insert,
                  beq_eq_false_iff_ne, hne, hval, hval']
          · rw [if_neg hc]
            simp [rowsFor, heldFor, fedFor, hbf, freshRun, Std.HashMap.getElem?_insert,
                  beq_eq_false_iff_ne, hne, hval, hval']

theorem pubAdd_rows (p : WfIri) (st : Pub) (quad : QuadRow) :
    rowsFor p (pubAdd st quad).2 ++ heldFor p (pubAdd st quad).1
      = heldFor p st ++ fedFor p [quad] := by
  rw [pubAdd_eq]
  by_cases hcarry : (pubAddRun st quad).1.carried > maxCarriedRows
  · rw [if_pos hcarry]
    rw [rowsFor_append, List.append_assoc,
        pubFlush_rows p (pubAddRun st quad).1 0]
    exact pubAddRun_rows p st quad
  · rw [if_neg hcarry]
    exact pubAddRun_rows p st quad

/-! ## A whole pass

An event list is one read of the source: each quad the grammar completed, in
source order, with a `flush` wherever a publication rule fired. The batch rule
(rule 3) is `flush minBatchRows` at a batch end; the end of source (rule 5) is
`flush 0`. Rules 2 and 4 are inside `pubAdd`, so they need no event. -/

inductive PubEvent where
  | quad (q : QuadRow)
  | flush (minRows : Nat)

def pubApply (acc : Pub × List (WfIri × List QuadRow)) :
    PubEvent → Pub × List (WfIri × List QuadRow)
  | .quad q => ((pubAdd acc.1 q).1, acc.2 ++ (pubAdd acc.1 q).2)
  | .flush n => ((pubFlush acc.1 n).1, acc.2 ++ (pubFlush acc.1 n).2)

def pubRunFrom (start : Pub × List (WfIri × List QuadRow))
    (events : List PubEvent) : Pub × List (WfIri × List QuadRow) :=
  events.foldl pubApply start

def pubRun (events : List PubEvent) : Pub × List (WfIri × List QuadRow) :=
  pubRunFrom ({}, []) events

/-- The quads an event list feeds, in source order. -/
def quadsOfEvents : List PubEvent → List QuadRow
  | [] => []
  | .quad q :: rest => q :: quadsOfEvents rest
  | .flush _ :: rest => quadsOfEvents rest

/-- The invariant of a pass, per predicate: what has been published plus what
    the open run still holds is exactly what has been fed, in source order. -/
theorem pubRunFrom_rows (p : WfIri) :
    ∀ (events : List PubEvent) (acc : Pub × List (WfIri × List QuadRow)),
      rowsFor p (pubRunFrom acc events).2 ++ heldFor p (pubRunFrom acc events).1
        = rowsFor p acc.2 ++ heldFor p acc.1 ++ fedFor p (quadsOfEvents events)
  | [], acc => by simp [pubRunFrom, quadsOfEvents, fedFor]
  | .quad q :: rest, acc => by
      have hstep : pubRunFrom acc (PubEvent.quad q :: rest)
          = pubRunFrom (pubApply acc (PubEvent.quad q)) rest := rfl
      rw [hstep, pubRunFrom_rows p rest (pubApply acc (PubEvent.quad q))]
      show rowsFor p (acc.2 ++ (pubAdd acc.1 q).2) ++ heldFor p (pubAdd acc.1 q).1
            ++ fedFor p (quadsOfEvents rest)
          = rowsFor p acc.2 ++ heldFor p acc.1 ++ fedFor p (quadsOfEvents (.quad q :: rest))
      rw [rowsFor_append,
          List.append_assoc (rowsFor p acc.2) (rowsFor p (pubAdd acc.1 q).2),
          pubAdd_rows p acc.1 q,
          show quadsOfEvents (PubEvent.quad q :: rest) = [q] ++ quadsOfEvents rest from rfl,
          fedFor_append]
      simp [List.append_assoc]
  | .flush n :: rest, acc => by
      have hstep : pubRunFrom acc (PubEvent.flush n :: rest)
          = pubRunFrom (pubApply acc (PubEvent.flush n)) rest := rfl
      rw [hstep, pubRunFrom_rows p rest (pubApply acc (PubEvent.flush n))]
      show rowsFor p (acc.2 ++ (pubFlush acc.1 n).2) ++ heldFor p (pubFlush acc.1 n).1
            ++ fedFor p (quadsOfEvents rest)
          = rowsFor p acc.2 ++ heldFor p acc.1 ++ fedFor p (quadsOfEvents (.flush n :: rest))
      rw [rowsFor_append,
          List.append_assoc (rowsFor p acc.2) (rowsFor p (pubFlush acc.1 n).2),
          pubFlush_rows p acc.1 n,
          show quadsOfEvents (PubEvent.flush n :: rest) = quadsOfEvents rest from rfl]

/-- The same statement from the start of a pass. -/
theorem pubRun_rows (p : WfIri) (events : List PubEvent) :
    rowsFor p (pubRun events).2 ++ heldFor p (pubRun events).1
      = fedFor p (quadsOfEvents events) := by
  have := pubRunFrom_rows p events (({} : Pub), [])
  simpa [pubRun, rowsFor, heldFor] using this


/-! ## The end of a pass: rule 5 empties every open run

`pubFlush st 0` walks `st.orderRev`, so it clears exactly the predicates that
list names. `PubOrdered` is the invariant that says it names them all. -/

/-- Every predicate with an open run is named by `orderRev`. -/
def PubOrdered (st : Pub) : Prop :=
  ∀ q : WfIri, (st.runs[q]?).isSome = true → q ∈ st.orderRev

theorem pubOrdered_empty : PubOrdered ({} : Pub) := by
  intro q hq
  simp at hq

private theorem flushStep_ordered (minRows : Nat)
    (acc : Pub × List (WfIri × List QuadRow)) (predicate : WfIri)
    (h : PubOrdered acc.1) : PubOrdered (flushStep minRows acc predicate).1 := by
  unfold flushStep
  cases hq : acc.1.runs[predicate]? with
  | none => exact h
  | some run =>
      dsimp only
      by_cases hskip : (run.accRev.isEmpty || decide (run.rows < minRows)) = true
      · rw [if_pos hskip]; exact h
      · rw [if_neg hskip]
        intro q hqs
        by_cases hpe : predicate = q
        · subst hpe; exact h predicate (by rw [hq]; rfl)
        · have hval : ¬ predicate.val = q.val := fun hv => hpe (Subtype.ext hv)
          refine h q ?_
          simpa [Std.HashMap.getElem?_insert, hval] using hqs

private theorem flushFold_ordered (minRows : Nat) :
    ∀ (ps : List WfIri) (acc : Pub × List (WfIri × List QuadRow)),
      PubOrdered acc.1 → PubOrdered (ps.foldl (flushStep minRows) acc).1
  | [], acc, h => h
  | a :: rest, acc, h => by
      simp only [List.foldl_cons]
      exact flushFold_ordered minRows rest _ (flushStep_ordered minRows acc a h)

theorem pubFlush_ordered (st : Pub) (minRows : Nat) (h : PubOrdered st) :
    PubOrdered (pubFlush st minRows).1 := by
  rw [pubFlush_eq]
  exact flushFold_ordered minRows st.orderRev.reverse (st, []) h

theorem pubAddRun_ordered (st : Pub) (quad : QuadRow) (h : PubOrdered st) :
    PubOrdered (pubAddRun st quad).1 := by
  rw [pubAddRun_eq]
  cases hq : st.runs[quad.2.p]? with
  | none =>
      intro q hqs
      by_cases hpe : quad.2.p = q
      · subst hpe; exact List.mem_cons_self ..
      · have hval : ¬ quad.2.p.val = q.val := fun hv => hpe (Subtype.ext hv)
        refine List.mem_cons_of_mem _ (h q ?_)
        simpa [Std.HashMap.getElem?_insert, hval] using hqs
  | some run =>
      dsimp only
      have hpres : ∀ (r : Run), PubOrdered { st with runs := st.runs.insert quad.2.p r } := by
        intro r q hqs
        by_cases hpe : quad.2.p = q
        · subst hpe; exact h quad.2.p (by rw [hq]; rfl)
        · have hval : ¬ quad.2.p.val = q.val := fun hv => hpe (Subtype.ext hv)
          refine h q ?_
          simpa [Std.HashMap.getElem?_insert, hval] using hqs
      by_cases he : run.accRev.isEmpty = true
      · rw [if_pos he]; exact hpres _
      · rw [if_neg he]
        by_cases hc : quad.1 == run.graph && run.rows < maxBlockRows &&
            run.bytes + quadWireBytes quad <= maxBlockWireBytes
        · rw [if_pos hc]; exact hpres _
        · rw [if_neg hc]; exact hpres _

theorem pubAdd_ordered (st : Pub) (quad : QuadRow) (h : PubOrdered st) :
    PubOrdered (pubAdd st quad).1 := by
  rw [pubAdd_eq]
  by_cases hcarry : (pubAddRun st quad).1.carried > maxCarriedRows
  · rw [if_pos hcarry]
    exact pubFlush_ordered _ 0 (pubAddRun_ordered st quad h)
  · rw [if_neg hcarry]
    exact pubAddRun_ordered st quad h

/-- Once a predicate's open run is empty, a flush keeps it empty. -/
private theorem flushFold_keeps_nil (p : WfIri) :
    ∀ (ps : List WfIri) (acc : Pub × List (WfIri × List QuadRow)),
      heldFor p acc.1 = [] → heldFor p (ps.foldl (flushStep 0) acc).1 = []
  | [], acc, h => h
  | a :: rest, acc, h => by
      simp only [List.foldl_cons]
      refine flushFold_keeps_nil p rest _ ?_
      unfold flushStep
      cases hq : acc.1.runs[a]? with
      | none => exact h
      | some run =>
          dsimp only
          by_cases hskip : (run.accRev.isEmpty || decide (run.rows < 0)) = true
          · rw [if_pos hskip]; exact h
          · rw [if_neg hskip]
            by_cases hpe : a = p
            · subst hpe; simp [heldFor]
            · have hval : ¬ a.val = p.val := fun hv => hpe (Subtype.ext hv)
              simpa [heldFor, Std.HashMap.getElem?_insert, hval] using h

/-- A flush at `minRows = 0` empties the open run of every predicate its
    order names. -/
private theorem flushFold_clears (p : WfIri) :
    ∀ (ps : List WfIri) (acc : Pub × List (WfIri × List QuadRow)),
      p ∈ ps → heldFor p (ps.foldl (flushStep 0) acc).1 = []
  | a :: rest, acc, hmem => by
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hmem with hpa | hrest
      · subst hpa
        refine flushFold_keeps_nil p rest _ ?_
        unfold flushStep
        cases hq : acc.1.runs[p]? with
        | none => simp [heldFor, hq]
        | some run =>
            dsimp only
            by_cases hskip : (run.accRev.isEmpty || decide (run.rows < 0)) = true
            · rw [if_pos hskip]
              have : run.accRev = [] := by
                simpa using hskip
              simp [heldFor, hq, this]
            · rw [if_neg hskip]; simp [heldFor]
      · exact flushFold_clears p rest _ hrest

theorem pubFlush_held_nil (p : WfIri) (st : Pub) (h : PubOrdered st) :
    heldFor p (pubFlush st 0).1 = [] := by
  rw [pubFlush_eq]
  by_cases hs : (st.runs[p]?).isSome = true
  · exact flushFold_clears p st.orderRev.reverse (st, [])
      (List.mem_reverse.mpr (h p hs))
  · refine flushFold_keeps_nil p st.orderRev.reverse (st, []) ?_
    cases hq : st.runs[p]? with
    | none => simp [heldFor, hq]
    | some run => rw [hq] at hs; simp at hs

theorem pubRunFrom_ordered :
    ∀ (events : List PubEvent) (acc : Pub × List (WfIri × List QuadRow)),
      PubOrdered acc.1 → PubOrdered (pubRunFrom acc events).1
  | [], acc, h => h
  | .quad q :: rest, acc, h => by
      show PubOrdered (pubRunFrom (pubApply acc (PubEvent.quad q)) rest).1
      exact pubRunFrom_ordered rest _ (pubAdd_ordered acc.1 q h)
  | .flush n :: rest, acc, h => by
      show PubOrdered (pubRunFrom (pubApply acc (PubEvent.flush n)) rest).1
      exact pubRunFrom_ordered rest _ (pubFlush_ordered acc.1 n h)

/-- The end-of-source statement. A pass that ends with rule 5 — `flush 0`,
    which `quadIngestFinish` always runs — publishes for every predicate
    exactly the fed quads of that predicate, in source order. Nothing is held
    back, nothing is published twice, nothing is reordered inside a
    predicate. -/
private theorem quadsOfEvents_flush :
    ∀ (events : List PubEvent) (n : Nat),
      quadsOfEvents (events ++ [PubEvent.flush n]) = quadsOfEvents events
  | [], n => rfl
  | .quad q :: rest, n => by
      simp only [List.cons_append, quadsOfEvents]
      rw [quadsOfEvents_flush rest n]
  | .flush m :: rest, n => by
      simp only [List.cons_append, quadsOfEvents]
      rw [quadsOfEvents_flush rest n]

theorem pubRun_published_eq_fed (p : WfIri) (events : List PubEvent) :
    rowsFor p (pubRun (events ++ [PubEvent.flush 0])).2
      = fedFor p (quadsOfEvents events) := by
  have hall := pubRun_rows p (events ++ [PubEvent.flush 0])
  have hquads := quadsOfEvents_flush events 0
  have hord : PubOrdered (pubRun events).1 :=
    pubRunFrom_ordered events (({} : Pub), []) pubOrdered_empty
  have hlast : pubRun (events ++ [PubEvent.flush 0])
      = pubApply (pubRun events) (PubEvent.flush 0) := by
    simp [pubRun, pubRunFrom, List.foldl_append]
  have hnil : heldFor p (pubRun (events ++ [PubEvent.flush 0])).1 = [] := by
    rw [hlast]
    exact pubFlush_held_nil p (pubRun events).1 hord
  rw [hquads] at hall
  rw [hnil] at hall
  simpa using hall

/-! ## The buffered route cuts the same rows

`runsOfBuckets` holds every row of a predicate to the end and cuts once.
`addQuads_rows` says which rows those are — the fed quads of that predicate,
in source order — and `chunkQuadRows_flatten` says the cut loses nothing. So
the buffered route's rows for a predicate are `fedFor p quads`, which is what
`pubRun_published_eq_fed` says the streamed route publishes. The two routes
publish the same rows for the same predicate in the same order; the block
BOUNDARIES and the block ORDER differ, and the manifest admits that. -/

theorem addQuad_rows (p : WfIri) (st : Buckets) (quad : QuadRow) :
    ((addQuad st quad).rows.getD p []).reverse
      = (st.rows.getD p []).reverse ++ fedFor p [quad] := by
  unfold addQuad
  by_cases hpe : quad.2.p = p
  · subst hpe
    simp [fedFor]
  · have hval : ¬ quad.2.p.val = p.val := fun hv => hpe (Subtype.ext hv)
    have hbf : (quad.2.p == p) = false := by
      simp only [beq_eq_false_iff_ne]; exact hpe
    simp [fedFor, hbf, hval, Std.HashMap.getD_insert]

theorem addQuads_rows (p : WfIri) :
    ∀ (quads : List QuadRow) (st : Buckets),
      ((addQuads st quads).rows.getD p []).reverse
        = (st.rows.getD p []).reverse ++ fedFor p quads
  | [], st => by simp [addQuads, fedFor]
  | q :: rest, st => by
      show ((addQuads (addQuad st q) rest).rows.getD p []).reverse = _
      rw [addQuads_rows p rest (addQuad st q), addQuad_rows p st q,
          show (q :: rest) = [q] ++ rest from rfl, fedFor_append,
          List.append_assoc]

/-- The buffered route's rows for one predicate, cut and flattened. -/
theorem buffered_rows (p : WfIri) (quads : List QuadRow) :
    (chunkQuadRows ((addQuads ({} : Buckets) quads).rows.getD p []).reverse).flatten
      = fedFor p quads := by
  rw [chunkQuadRows_flatten, addQuads_rows p quads ({} : Buckets)]
  simp

/-- The two routes publish the same rows for the same predicate, in the same
    order: streamed publication moves no row. -/
theorem streamed_eq_buffered (p : WfIri) (events : List PubEvent) :
    rowsFor p (pubRun (events ++ [PubEvent.flush 0])).2
      = (chunkQuadRows
          ((addQuads ({} : Buckets) (quadsOfEvents events)).rows.getD p []).reverse).flatten := by
  rw [buffered_rows p (quadsOfEvents events)]
  exact pubRun_published_eq_fed p events

/-! ## Transport: a permutation of the rows keeps every graph's triples

The block SET differs between the two routes, so the flattened row order over
ALL predicates differs. This is what that costs: nothing, at the level a
dataset is read, because graph membership is invariant under permutation. -/

/-- The triples one graph's rows carry, in row order. -/
def graphTriples (g : Option GraphRef) (rows : List QuadRow) : List Triple :=
  rows.filterMap (fun quad => if quad.1 == g then some quad.2 else none)

theorem graphTriples_perm {a b : List QuadRow} (h : a.Perm b) (g : Option GraphRef) :
    (graphTriples g a).Perm (graphTriples g b) :=
  h.filterMap _

theorem mem_graphTriples_of_perm {a b : List QuadRow} (h : a.Perm b)
    (g : Option GraphRef) (t : Triple) :
    t ∈ graphTriples g a ↔ t ∈ graphTriples g b :=
  (graphTriples_perm h g).mem_iff

#print axioms pubRun_rows
#print axioms pubRun_published_eq_fed
#print axioms streamed_eq_buffered
#print axioms mem_graphTriples_of_perm

end L4Factoidal.Storage.PredicateQuadBlocks
