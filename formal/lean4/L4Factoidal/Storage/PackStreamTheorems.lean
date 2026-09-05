/-
Publishing IBK4 blocks DURING the ingest pass moves no row.

`docs/designissues/2026-09-05-pack-publication-every-batch.md` records the
policy. This file states what it preserves. The buffered route holds every
row of every bucket to the end of the source and cuts each bucket's
rows once (`runsOfBuckets`); the streamed route cuts the same rows as they
arrive and publishes each block as the cut rule closes it, with three further
publication rules that depend on the source bytes fed so far. The block SET
therefore differs. What must not differ is the rows.

The theorem below is stated PER BUCKET KEY — a (predicate, graph) pair since
2026-09-05 — over an event list which is a
source read plus its flush points:

  rowsFor k (published) ++ heldFor k (state) = fedFor k (quads)

for every key `k` and every prefix of the pass — nothing published is
absent from the fed quads, nothing fed is absent from the published rows plus
the open run, and the ORDER inside a key is the source order.
`pubRun_published_eq_fed` is the end-of-source corollary, where the open runs
are empty because rule 5 has flushed them.

`PredicateQuadBlocksTheorems.chunkQuadRows_flatten` is the same statement for
the buffered route. The two together say the streamed and the buffered routes
publish the same rows for the same key in the same order, so the union
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

/-- The rows published for one key, in publication order. -/
def rowsFor (k : BucketKey) (published : List (BucketKey × List QuadRow)) : List QuadRow :=
  published.flatMap fun entry => if entry.1 == k then entry.2 else []

/-- The rows one key's open run still holds, in source order. -/
def heldFor (k : BucketKey) (st : Pub) : List QuadRow :=
  match st.runs[k]? with
  | none => []
  | some run => run.accRev.reverse

/-- The fed quads whose key is `k`, in source order. -/
def fedFor (k : BucketKey) (quads : List QuadRow) : List QuadRow :=
  quads.filter (fun quad => keyOf quad == k)

theorem rowsFor_append (k : BucketKey) (a b : List (BucketKey × List QuadRow)) :
    rowsFor k (a ++ b) = rowsFor k a ++ rowsFor k b := by
  simp [rowsFor]

theorem rowsFor_nil (k : BucketKey) : rowsFor k [] = [] := rfl

theorem fedFor_append (k : BucketKey) (a b : List QuadRow) :
    fedFor k (a ++ b) = fedFor k a ++ fedFor k b := by
  simp [fedFor]

/-! ## A flush moves rows from the open runs to the published list -/

/-- One flush step preserves "published for `k`, then still held for `k`". -/
private theorem flushStep_inv (k : BucketKey) (minRows : Nat)
    (acc : Pub × List (BucketKey × List QuadRow)) (key : BucketKey) :
    rowsFor k (flushStep minRows acc key).2.reverse
        ++ heldFor k (flushStep minRows acc key).1
      = rowsFor k acc.2.reverse ++ heldFor k acc.1 := by
  unfold flushStep
  cases hq : acc.1.runs[key]? with
  | none => rfl
  | some run =>
      dsimp only
      by_cases hskip : (run.accRev.isEmpty || decide (run.rows < minRows)) = true
      · rw [if_pos hskip]
      · rw [if_neg hskip]
        by_cases hpe : key = k
        · subst hpe
          simp [rowsFor, heldFor, hq]
        · have hbf : (key == k) = false := by
            simp only [beq_eq_false_iff_ne]
            exact hpe
          simp [rowsFor, heldFor, hbf, hpe, Std.HashMap.getElem?_insert]

private theorem flushFold_inv (k : BucketKey) (minRows : Nat) :
    ∀ (ps : List BucketKey) (acc : Pub × List (BucketKey × List QuadRow)),
      rowsFor k (ps.foldl (flushStep minRows) acc).2.reverse
          ++ heldFor k (ps.foldl (flushStep minRows) acc).1
        = rowsFor k acc.2.reverse ++ heldFor k acc.1
  | [], acc => rfl
  | a :: rest, acc => by
      simp only [List.foldl_cons]
      rw [flushFold_inv k minRows rest (flushStep minRows acc a)]
      exact flushStep_inv k minRows acc a

/-- A flush publishes exactly what it releases: the rows for a key,
    published and still held, are unchanged by it. -/
theorem pubFlush_rows (k : BucketKey) (st : Pub) (minRows : Nat) :
    rowsFor k (pubFlush st minRows).2 ++ heldFor k (pubFlush st minRows).1
      = heldFor k st := by
  have h := flushFold_inv k minRows st.orderRev.reverse (st, [])
  rw [pubFlush_eq]
  simpa [rowsFor] using h

/-! ## One quad enters exactly one open run -/

theorem pubAddRun_rows (k : BucketKey) (st : Pub) (quad : QuadRow) :
    rowsFor k (pubAddRun st quad).2 ++ heldFor k (pubAddRun st quad).1
      = heldFor k st ++ fedFor k [quad] := by
  rw [pubAddRun_eq]
  by_cases hpe : keyOf quad = k
  · have hqp : keyOf quad = k := hpe
    cases hq : st.runs[keyOf quad]? with
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
          by_cases hc : run.rows < maxBlockRows &&
              run.bytes + quadWireBytes quad <= maxBlockWireBytes
          · rw [if_pos hc]
            subst hqp
            simp [rowsFor, heldFor, hq, fedFor]
          · rw [if_neg hc]
            subst hqp
            simp [rowsFor, heldFor, hq, fedFor, freshRun]
  · have hbf : (keyOf quad == k) = false := by
      simp only [beq_eq_false_iff_ne]; exact hpe
    cases hq : st.runs[keyOf quad]? with
    | none =>
        simp [rowsFor, heldFor, fedFor, hbf,
              Std.HashMap.getElem?_insert]
    | some run =>
        dsimp only
        by_cases he : run.accRev.isEmpty = true
        · rw [if_pos he]
          simp [rowsFor, heldFor, fedFor, hbf,
                Std.HashMap.getElem?_insert]
        · rw [if_neg he]
          by_cases hc : run.rows < maxBlockRows &&
              run.bytes + quadWireBytes quad <= maxBlockWireBytes
          · rw [if_pos hc]
            simp [rowsFor, heldFor, fedFor, hbf,
                  Std.HashMap.getElem?_insert]
          · rw [if_neg hc]
            simp [rowsFor, heldFor, fedFor, hbf, hpe,
                  Std.HashMap.getElem?_insert]

theorem pubAdd_rows (k : BucketKey) (st : Pub) (quad : QuadRow) :
    rowsFor k (pubAdd st quad).2 ++ heldFor k (pubAdd st quad).1
      = heldFor k st ++ fedFor k [quad] := by
  rw [pubAdd_eq]
  by_cases hcarry : (pubAddRun st quad).1.carried > maxCarriedRows
  · rw [if_pos hcarry]
    rw [rowsFor_append, List.append_assoc,
        pubFlush_rows k (pubAddRun st quad).1 0]
    exact pubAddRun_rows k st quad
  · rw [if_neg hcarry]
    exact pubAddRun_rows k st quad

/-! ## A whole pass

An event list is one read of the source: each quad the grammar completed, in
source order, with a `flush` wherever a publication rule fired. The batch rule
(rule 3) is `flush minBatchRows` at a batch end; the end of source (rule 5) is
`flush 0`. Rules 2 and 4 are inside `pubAdd`, so they need no event. -/

inductive PubEvent where
  | quad (q : QuadRow)
  | flush (minRows : Nat)

def pubApply (acc : Pub × List (BucketKey × List QuadRow)) :
    PubEvent → Pub × List (BucketKey × List QuadRow)
  | .quad q => ((pubAdd acc.1 q).1, acc.2 ++ (pubAdd acc.1 q).2)
  | .flush n => ((pubFlush acc.1 n).1, acc.2 ++ (pubFlush acc.1 n).2)

def pubRunFrom (start : Pub × List (BucketKey × List QuadRow))
    (events : List PubEvent) : Pub × List (BucketKey × List QuadRow) :=
  events.foldl pubApply start

def pubRun (events : List PubEvent) : Pub × List (BucketKey × List QuadRow) :=
  pubRunFrom ({}, []) events

/-- The quads an event list feeds, in source order. -/
def quadsOfEvents : List PubEvent → List QuadRow
  | [] => []
  | .quad q :: rest => q :: quadsOfEvents rest
  | .flush _ :: rest => quadsOfEvents rest

/-- The invariant of a pass, per key: what has been published plus what
    the open run still holds is exactly what has been fed, in source order. -/
theorem pubRunFrom_rows (k : BucketKey) :
    ∀ (events : List PubEvent) (acc : Pub × List (BucketKey × List QuadRow)),
      rowsFor k (pubRunFrom acc events).2 ++ heldFor k (pubRunFrom acc events).1
        = rowsFor k acc.2 ++ heldFor k acc.1 ++ fedFor k (quadsOfEvents events)
  | [], acc => by simp [pubRunFrom, quadsOfEvents, fedFor]
  | .quad q :: rest, acc => by
      have hstep : pubRunFrom acc (PubEvent.quad q :: rest)
          = pubRunFrom (pubApply acc (PubEvent.quad q)) rest := rfl
      rw [hstep, pubRunFrom_rows k rest (pubApply acc (PubEvent.quad q))]
      show rowsFor k (acc.2 ++ (pubAdd acc.1 q).2) ++ heldFor k (pubAdd acc.1 q).1
            ++ fedFor k (quadsOfEvents rest)
          = rowsFor k acc.2 ++ heldFor k acc.1 ++ fedFor k (quadsOfEvents (.quad q :: rest))
      rw [rowsFor_append,
          List.append_assoc (rowsFor k acc.2) (rowsFor k (pubAdd acc.1 q).2),
          pubAdd_rows k acc.1 q,
          show quadsOfEvents (PubEvent.quad q :: rest) = [q] ++ quadsOfEvents rest from rfl,
          fedFor_append]
      simp [List.append_assoc]
  | .flush n :: rest, acc => by
      have hstep : pubRunFrom acc (PubEvent.flush n :: rest)
          = pubRunFrom (pubApply acc (PubEvent.flush n)) rest := rfl
      rw [hstep, pubRunFrom_rows k rest (pubApply acc (PubEvent.flush n))]
      show rowsFor k (acc.2 ++ (pubFlush acc.1 n).2) ++ heldFor k (pubFlush acc.1 n).1
            ++ fedFor k (quadsOfEvents rest)
          = rowsFor k acc.2 ++ heldFor k acc.1 ++ fedFor k (quadsOfEvents (.flush n :: rest))
      rw [rowsFor_append,
          List.append_assoc (rowsFor k acc.2) (rowsFor k (pubFlush acc.1 n).2),
          pubFlush_rows k acc.1 n,
          show quadsOfEvents (PubEvent.flush n :: rest) = quadsOfEvents rest from rfl]

/-- The same statement from the start of a pass. -/
theorem pubRun_rows (k : BucketKey) (events : List PubEvent) :
    rowsFor k (pubRun events).2 ++ heldFor k (pubRun events).1
      = fedFor k (quadsOfEvents events) := by
  have := pubRunFrom_rows k events (({} : Pub), [])
  simpa [pubRun, rowsFor, heldFor] using this


/-! ## The end of a pass: rule 5 empties every open run

`pubFlush st 0` walks `st.orderRev`, so it clears exactly the predicates that
list names. `PubOrdered` is the invariant that says it names them all. -/

/-- Every key with an open run is named by `orderRev`. -/
def PubOrdered (st : Pub) : Prop :=
  ∀ q : BucketKey, (st.runs[q]?).isSome = true → q ∈ st.orderRev

theorem pubOrdered_empty : PubOrdered ({} : Pub) := by
  intro q hq
  simp at hq

private theorem flushStep_ordered (minRows : Nat)
    (acc : Pub × List (BucketKey × List QuadRow)) (key : BucketKey)
    (h : PubOrdered acc.1) : PubOrdered (flushStep minRows acc key).1 := by
  unfold flushStep
  cases hq : acc.1.runs[key]? with
  | none => exact h
  | some run =>
      dsimp only
      by_cases hskip : (run.accRev.isEmpty || decide (run.rows < minRows)) = true
      · rw [if_pos hskip]; exact h
      · rw [if_neg hskip]
        intro q hqs
        by_cases hpe : key = q
        · subst hpe; exact h key (by rw [hq]; rfl)
        · have hbf : (key == q) = false := by
            simp only [beq_eq_false_iff_ne]; exact hpe
          refine h q ?_
          simpa [Std.HashMap.getElem?_insert, hbf] using hqs

private theorem flushFold_ordered (minRows : Nat) :
    ∀ (ps : List BucketKey) (acc : Pub × List (BucketKey × List QuadRow)),
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
  cases hq : st.runs[keyOf quad]? with
  | none =>
      intro q hqs
      by_cases hpe : keyOf quad = q
      · subst hpe; exact List.mem_cons_self ..
      · have hbf : (keyOf quad == q) = false := by
          simp only [beq_eq_false_iff_ne]; exact hpe
        refine List.mem_cons_of_mem _ (h q ?_)
        simpa [Std.HashMap.getElem?_insert, hbf] using hqs
  | some run =>
      dsimp only
      have hpres : ∀ (r : Run), PubOrdered { st with runs := st.runs.insert (keyOf quad) r } := by
        intro r q hqs
        by_cases hpe : keyOf quad = q
        · subst hpe; exact h (keyOf quad) (by rw [hq]; rfl)
        · have hbf : (keyOf quad == q) = false := by
            simp only [beq_eq_false_iff_ne]; exact hpe
          refine h q ?_
          simpa [Std.HashMap.getElem?_insert, hbf] using hqs
      by_cases he : run.accRev.isEmpty = true
      · rw [if_pos he]; exact hpres _
      · rw [if_neg he]
        by_cases hc : run.rows < maxBlockRows &&
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

/-- Once a key's open run is empty, a flush keeps it empty. -/
private theorem flushFold_keeps_nil (k : BucketKey) :
    ∀ (ps : List BucketKey) (acc : Pub × List (BucketKey × List QuadRow)),
      heldFor k acc.1 = [] → heldFor k (ps.foldl (flushStep 0) acc).1 = []
  | [], acc, h => h
  | a :: rest, acc, h => by
      simp only [List.foldl_cons]
      refine flushFold_keeps_nil k rest _ ?_
      unfold flushStep
      cases hq : acc.1.runs[a]? with
      | none => exact h
      | some run =>
          dsimp only
          by_cases hskip : (run.accRev.isEmpty || decide (run.rows < 0)) = true
          · rw [if_pos hskip]; exact h
          · rw [if_neg hskip]
            by_cases hpe : a = k
            · subst hpe; simp [heldFor]
            · have hbf : (a == k) = false := by
                simp only [beq_eq_false_iff_ne]; exact hpe
              simpa [heldFor, Std.HashMap.getElem?_insert, hbf] using h

/-- A flush at `minRows = 0` empties the open run of every key its
    order names. -/
private theorem flushFold_clears (k : BucketKey) :
    ∀ (ps : List BucketKey) (acc : Pub × List (BucketKey × List QuadRow)),
      k ∈ ps → heldFor k (ps.foldl (flushStep 0) acc).1 = []
  | a :: rest, acc, hmem => by
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hmem with hpa | hrest
      · subst hpa
        refine flushFold_keeps_nil k rest _ ?_
        unfold flushStep
        cases hq : acc.1.runs[k]? with
        | none => simp [heldFor, hq]
        | some run =>
            dsimp only
            by_cases hskip : (run.accRev.isEmpty || decide (run.rows < 0)) = true
            · rw [if_pos hskip]
              have : run.accRev = [] := by
                simpa using hskip
              simp [heldFor, hq, this]
            · rw [if_neg hskip]; simp [heldFor]
      · exact flushFold_clears k rest _ hrest

theorem pubFlush_held_nil (k : BucketKey) (st : Pub) (h : PubOrdered st) :
    heldFor k (pubFlush st 0).1 = [] := by
  rw [pubFlush_eq]
  by_cases hs : (st.runs[k]?).isSome = true
  · exact flushFold_clears k st.orderRev.reverse (st, [])
      (List.mem_reverse.mpr (h k hs))
  · refine flushFold_keeps_nil k st.orderRev.reverse (st, []) ?_
    cases hq : st.runs[k]? with
    | none => simp [heldFor, hq]
    | some run => rw [hq] at hs; simp at hs

theorem pubRunFrom_ordered :
    ∀ (events : List PubEvent) (acc : Pub × List (BucketKey × List QuadRow)),
      PubOrdered acc.1 → PubOrdered (pubRunFrom acc events).1
  | [], acc, h => h
  | .quad q :: rest, acc, h => by
      show PubOrdered (pubRunFrom (pubApply acc (PubEvent.quad q)) rest).1
      exact pubRunFrom_ordered rest _ (pubAdd_ordered acc.1 q h)
  | .flush n :: rest, acc, h => by
      show PubOrdered (pubRunFrom (pubApply acc (PubEvent.flush n)) rest).1
      exact pubRunFrom_ordered rest _ (pubFlush_ordered acc.1 n h)

/-- The end-of-source statement. A pass that ends with rule 5 — `flush 0`,
    which `quadIngestFinish` always runs — publishes for every key
    exactly the fed quads of that key, in source order. Nothing is held
    back, nothing is published twice, nothing is reordered inside a
    key. -/
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

theorem pubRun_published_eq_fed (k : BucketKey) (events : List PubEvent) :
    rowsFor k (pubRun (events ++ [PubEvent.flush 0])).2
      = fedFor k (quadsOfEvents events) := by
  have hall := pubRun_rows k (events ++ [PubEvent.flush 0])
  have hquads := quadsOfEvents_flush events 0
  have hord : PubOrdered (pubRun events).1 :=
    pubRunFrom_ordered events (({} : Pub), []) pubOrdered_empty
  have hlast : pubRun (events ++ [PubEvent.flush 0])
      = pubApply (pubRun events) (PubEvent.flush 0) := by
    simp [pubRun, pubRunFrom, List.foldl_append]
  have hnil : heldFor k (pubRun (events ++ [PubEvent.flush 0])).1 = [] := by
    rw [hlast]
    exact pubFlush_held_nil k (pubRun events).1 hord
  rw [hquads] at hall
  rw [hnil] at hall
  simpa using hall

/-! ## The buffered route cuts the same rows

`runsOfBuckets` holds every row of a key to the end and cuts once.
`addQuads_rows` says which rows those are — the fed quads of that key,
in source order — and `chunkQuadRows_flatten` says the cut loses nothing. So
the buffered route's rows for a key are `fedFor k quads`, which is what
`pubRun_published_eq_fed` says the streamed route publishes. The two routes
publish the same rows for the same key in the same order; the block
BOUNDARIES and the block ORDER differ, and the manifest admits that. -/

theorem addQuad_rows (k : BucketKey) (st : Buckets) (quad : QuadRow) :
    ((addQuad st quad).rows.getD k []).reverse
      = (st.rows.getD k []).reverse ++ fedFor k [quad] := by
  unfold addQuad
  by_cases hpe : keyOf quad = k
  · subst hpe
    simp [fedFor]
  · have hbf : (keyOf quad == k) = false := by
      simp only [beq_eq_false_iff_ne]; exact hpe
    simp [fedFor, hbf, Std.HashMap.getD_insert]

theorem addQuads_rows (k : BucketKey) :
    ∀ (quads : List QuadRow) (st : Buckets),
      ((addQuads st quads).rows.getD k []).reverse
        = (st.rows.getD k []).reverse ++ fedFor k quads
  | [], st => by simp [addQuads, fedFor]
  | q :: rest, st => by
      show ((addQuads (addQuad st q) rest).rows.getD k []).reverse = _
      rw [addQuads_rows k rest (addQuad st q), addQuad_rows k st q,
          show (q :: rest) = [q] ++ rest from rfl, fedFor_append,
          List.append_assoc]

/-- The buffered route's rows for one key, cut and flattened. -/
theorem buffered_rows (k : BucketKey) (quads : List QuadRow) :
    (chunkQuadRows ((addQuads ({} : Buckets) quads).rows.getD k []).reverse).flatten
      = fedFor k quads := by
  rw [chunkQuadRows_flatten, addQuads_rows k quads ({} : Buckets)]
  simp

/-- The two routes publish the same rows for the same key, in the same
    order: streamed publication moves no row. -/
theorem streamed_eq_buffered (k : BucketKey) (events : List PubEvent) :
    rowsFor k (pubRun (events ++ [PubEvent.flush 0])).2
      = (chunkQuadRows
          ((addQuads ({} : Buckets) (quadsOfEvents events)).rows.getD k []).reverse).flatten := by
  rw [buffered_rows k (quadsOfEvents events)]
  exact pubRun_published_eq_fed k events

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
