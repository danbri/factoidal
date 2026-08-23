/-
L4Factoidal.RDF.StoreCapabilitiesDelta — the delta overlay.

Port of `formal/fstar/RDF.Store.Capabilities.Delta.fst` (138 lines).

`overlay` turns any read seam plus one graph's resolved delta into
another read seam OF THE SAME TYPE. There is no new backend
constructor and no new optional field: the evaluator never learns a
delta exists.

It is a sibling module rather than part of `RDF.StoreCapabilities`
itself, matching the F\* split, so that the base module keeps its narrow
contract — types and the in-memory builder only.

## An empty delta is a no-op by construction

The `deltaResolvedIsEmpty` branch returns the wrapped seam with one
flag flipped. That is what makes "an empty delta costs nothing" exact:
it is this function's own short circuit, not an optimisation layered
over a general path.

## Two capabilities are withdrawn while a delta is live, for opposite
reasons

`distinctPredicates` becomes `none`. The base's dictionary pages were
written when the base file was compacted and cannot mention a predicate
that exists only in the delta. Enumerating from them would DROP a whole
GROUP BY row, which is a wrong answer rather than a slow one, so the
caller is sent back to the path that reads rows.

`solveSelective` stays `some` and ignores both `need` and the base's own
accelerated call, re-running the same merge `solve` does. It cannot go
`none`, because this field stands in for `solve` and a caller that skips
a `none` member drops rows. So it is correct and simply not accelerated
while a delta is live.

Both revert to the base's own behaviour in the empty-delta branch, which
is right: an empty delta changes nothing either could have missed.
-/
import L4Factoidal.RDF.StoreDeltaMerge

namespace L4Factoidal.RDF

open L4Factoidal.SPARQL (PatternBound patternBoundAll tripleMatchesBound)

/-- Base read seam plus one graph's resolved delta, as a read seam. -/
def overlay (base : StoreCaps) (delta : DeltaResolved) : StoreCaps :=
  if deltaResolvedIsEmpty delta then
    { base with flags := { base.flags with supportsUpdate := true } }
  else
    { flags := { base.flags with supportsUpdate := true }
      -- pure composition on top of whatever the base already returns
    , solve := fun b => mergeOnRead (base.solve b) delta b
      -- no real pushdown once a delta is in play: solve the merged view
      -- for this bound, then truncate
    , solveLimited := fun b n => capsTakeN n (mergeOnRead (base.solve b) delta b)
      -- additive in the delta only; never re-touches the base results
    , estimate := fun b => base.estimate b + deltaMatchingCount delta b
      -- recomputed through the merged view rather than by
      -- base-count-plus-or-minus-delta arithmetic. The arithmetic form
      -- would need `base.countExact b` and `(base.solve b).length` to be
      -- equal, which holds for no arbitrary seam. The cost is
      -- materialising `base.solve b`, which `solve` above already pays
      -- for this bound — not a second materialisation.
    , countExact := fun b => (mergeOnRead (base.solve b) delta b).length
      -- conservative OR: never a false negative
    , predicatePresent := fun pred =>
        base.predicatePresent pred || deltaAddedHasPredicate delta.added pred
      -- the delta layer introduces no decode failures of its own
    , decodeFailure := base.decodeFailure
    , distinctPredicates := none
    , solveSelective := some (fun b _need => mergeOnRead (base.solve b) delta b) }

/-- The store view: a base seam with a delta is read-write, so it
carries a write seam. `applyDelta` is where durability lives; the bytes
it writes are specified in `Storage.DeltaLog`. -/
def storeOfOverlay (base : StoreCaps) (delta : DeltaResolved)
    (write : StoreWriteCaps) : Store :=
  { read := overlay base delta, write := some write }

/-! ## Build-time checks -/

section Checks

private def iriW (s : String) : WfIri :=
  if h : isIri s then ⟨s, h⟩ else ⟨"http://e.org/", by decide⟩

private def u1 : Triple := ⟨.iri (iriW "http://e.org/a"), iriW "http://e.org/p",
                            .iri (iriW "http://e.org/1")⟩
private def u2 : Triple := ⟨.iri (iriW "http://e.org/b"), iriW "http://e.org/p",
                            .iri (iriW "http://e.org/2")⟩
private def u3 : Triple := ⟨.iri (iriW "http://e.org/c"), iriW "http://e.org/q",
                            .iri (iriW "http://e.org/3")⟩

private def baseCaps : StoreCaps := capsOfIndexed (OWL.RL.Index.ofGraph [u1, u2])

private def fold (es : List Storage.DeltaEntry) : DeltaResolved :=
  foldEntriesForGraph none es deltaResolvedEmpty

/-! ### An empty delta changes NOTHING a caller can observe, except that
the store now advertises a write path. -/

private def emptyOverlay : StoreCaps := overlay baseCaps deltaResolvedEmpty

#guard emptyOverlay.solve patternBoundAll == baseCaps.solve patternBoundAll
#guard emptyOverlay.countExact patternBoundAll == baseCaps.countExact patternBoundAll
#guard emptyOverlay.estimate patternBoundAll == baseCaps.estimate patternBoundAll
#guard emptyOverlay.solveLimited patternBoundAll 1 == baseCaps.solveLimited patternBoundAll 1
#guard emptyOverlay.distinctPredicates.isNone == baseCaps.distinctPredicates.isNone
#guard emptyOverlay.solveSelective.isNone == baseCaps.solveSelective.isNone
#guard emptyOverlay.flags.supportsUpdate

/-! ### A live delta adds, tombstones and clears -/

private def addOverlay : StoreCaps := overlay baseCaps (fold [.add u3 none])
private def delOverlay : StoreCaps := overlay baseCaps (fold [.remove u1 none])
private def clrOverlay : StoreCaps := overlay baseCaps (fold [.clear none])

#guard addOverlay.solve patternBoundAll == [u1, u2, u3]
#guard delOverlay.solve patternBoundAll == [u2]
#guard clrOverlay.solve patternBoundAll == []
#guard addOverlay.countExact patternBoundAll == 3
#guard delOverlay.countExact patternBoundAll == 1
#guard clrOverlay.countExact patternBoundAll == 0

/-! ### The estimate is the base plus the delta's matching additions. It
is NOT claimed exact under a tombstone: `delOverlay` estimates 2 while
the exact count is 1, which is the approximation the flag allows. -/

#guard addOverlay.estimate patternBoundAll == 3
#guard delOverlay.estimate patternBoundAll == 2
#guard delOverlay.countExact patternBoundAll == 1

/-! ### DISTINCT-predicate enumeration is WITHDRAWN under a live delta,
and inherited when the delta is empty. -/

#guard addOverlay.distinctPredicates.isNone
#guard emptyOverlay.distinctPredicates.isNone == baseCaps.distinctPredicates.isNone

/-! ### Selective solve is always offered under a live delta, and returns
the same rows as plain solve at every `ColNeed`. -/

#guard addOverlay.solveSelective.isSome

private def selAgrees (caps : StoreCaps) (need : ColNeed) : Bool :=
  match caps.solveSelective with
  | none   => true
  | some f => f patternBoundAll need == caps.solve patternBoundAll

#guard selAgrees addOverlay colNeedAll
#guard selAgrees addOverlay colNeedNone
#guard selAgrees delOverlay colNeedNone
#guard selAgrees clrOverlay colNeedAll

/-! ### Presence is conservative: the delta's own predicate is found,
and a tombstoned one may still report present — the safe direction. -/

#guard addOverlay.predicatePresent (iriW "http://e.org/q")
#guard delOverlay.predicatePresent (iriW "http://e.org/p")

/-! ### LIMIT truncates the merged view -/

#guard addOverlay.solveLimited patternBoundAll 2 == [u1, u2]
#guard addOverlay.solveLimited patternBoundAll 0 == []

/-! ### The bound applies to the delta's additions too -/

#guard addOverlay.solve { p := some (iriW "http://e.org/q") } == [u3]

end Checks

end L4Factoidal.RDF
