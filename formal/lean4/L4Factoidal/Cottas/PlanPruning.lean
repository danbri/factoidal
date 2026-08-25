/-
L4Factoidal.Cottas.PlanPruning — the row-group prune predicate.

Port of `formal/fstar/SPARQL.Plan.Pruning.fst` (256 lines). Recovery-plan
phase 4: it retires three codename violators into one descriptive home —
the predicate-presence skip, the subject-and-object skip, and the
compound joint-(p, o) skip, which had been ~900 lines of OCaml consulting
`Hashtbl` mirrors of data the writer already put on disk. An OCaml side
deciding "skip this row group" is a backend correctness decision, which
iron rule #11 puts in the formal source.

## What it composes

| Gate | Question |
|---|---|
| subject | does row group `rg` hold the bound subject token at all? |
| predicate | same for the predicate column |
| object | same for the object column |
| compound (p, o) | does it hold them in the SAME ROW? |

The compound gate is strictly more selective than the per-column AND: a
row group can hold predicate `p` in one row and object `o` in another
and never both together. The three per-column gates cannot see that.

## Soundness composes, and no new lemma is needed

`rgCanMatch` is a boolean AND. When it is `false`, exactly one conjunct
is `false`, and that conjunct's own soundness lemma —
`rgContainsToken_sound` or `rgCouldContainPair_sound` — says the row
group holds no matching row. So skipping it is sound.

Both of those lemmas carry the same open producer-side obligation: they
hold GIVEN that the on-disk file agrees with the ground truth, and
nothing in either tree shows that of any actual file. The writer is in
OCaml. This module inherits that gap rather than adding to it.

## The `(s, p)` variant reuses the `(p, o)` reader

The compound file format pairs two ids by lexicographic sort and is
column-agnostic at the type level: whichever id the caller passes first
occupies the high 32 bits. `compoundSpCanMatch` therefore calls the same
reader with `(boundS, boundP)`. The caller passes the handle for whichever
compound file it opened, and passing the wrong one is not a type error —
the F\* module has the same property, and it is worth naming.
-/
import L4Factoidal.Cottas.CompoundPresenceBitmap

namespace L4Factoidal.Cottas

/-- The resolved token ids of a triple pattern's three positions.
    `none` is an unbound position. Resolution from pattern terms to
    token ids is the dictionary's job, upstream of this module — which
    is why nothing here depends on the SPARQL algebra. -/
structure PatternBoundIds where
  s : Option Nat
  p : Option Nat
  o : Option Nat
  deriving Repr, DecidableEq, Inhabited

def noBounds : PatternBoundIds := { s := none, p := none, o := none }

def mkBounds (s p o : Option Nat) : PatternBoundIds := { s := s, p := p, o := o }

/-! ## The per-column gates

Three names for one call, kept distinct so a call site reads like the
plan it implements. -/

def predicateCanMatch (ohP : Option BitmapHandle) (rg : Nat) (boundP : Option Nat) :
    Bool := rgCouldContain ohP rg boundP

def subjectCanMatch (ohS : Option BitmapHandle) (rg : Nat) (boundS : Option Nat) :
    Bool := rgCouldContain ohS rg boundS

def objectCanMatch (ohO : Option BitmapHandle) (rg : Nat) (boundO : Option Nat) :
    Bool := rgCouldContain ohO rg boundO

/-! ## The compound gates -/

def compoundPoCanMatch (ohCompound : Option CompoundHandle) (rg : Nat)
    (boundP boundO : Option Nat) : Bool :=
  compoundRgPassesPair ohCompound rg boundP boundO

/-- See the module header: the compound reader is column-agnostic, so
    the `(s, p)` bitmap uses the same one with the subject id in the
    high slot. -/
def compoundSpCanMatch (ohCompound : Option CompoundHandle) (rg : Nat)
    (boundS boundP : Option Nat) : Bool :=
  compoundRgPassesPair ohCompound rg boundS boundP

/-! ## The top-level predicate

`true` means the row group cannot be ruled out and should be scanned.
`false` means at least one gate decisively ruled it out. -/

def rgCanMatch (rg : Nat)
    (ohS : Option BitmapHandle) (boundS : Option Nat)
    (ohP : Option BitmapHandle) (boundP : Option Nat)
    (ohO : Option BitmapHandle) (boundO : Option Nat)
    (ohCompoundPo : Option CompoundHandle) : Bool :=
  rgPassesAll rg ohS boundS ohP boundP ohO boundO &&
  compoundRgPassesPair ohCompoundPo rg boundP boundO

def rgCanMatchForPattern (rg : Nat) (bounds : PatternBoundIds)
    (ohS ohP ohO : Option BitmapHandle)
    (ohCompoundPo : Option CompoundHandle) : Bool :=
  rgCanMatch rg ohS bounds.s ohP bounds.p ohO bounds.o ohCompoundPo

/-- Filter a candidate row-group list. Order is preserved. -/
def filterCandidatesByPrune (candidates : List Nat)
    (ohS : Option BitmapHandle) (boundS : Option Nat)
    (ohP : Option BitmapHandle) (boundP : Option Nat)
    (ohO : Option BitmapHandle) (boundO : Option Nat)
    (ohCompoundPo : Option CompoundHandle) : List Nat :=
  candidates.filter (fun rg =>
    rgCanMatch rg ohS boundS ohP boundP ohO boundO ohCompoundPo)

/-! ## The identity property

With nothing bound and no companion open, every row group passes. This
is the "no opinion means include everything" guarantee the prune callers
rely on: turning the optimisation off must not change any answer. -/

theorem rgCanMatch_all_unbound (rg : Nat) :
    rgCanMatch rg none none none none none none none = true := by
  simp [rgCanMatch, rgPassesAll, rgCouldContain, compoundRgPassesPair]

theorem filterCandidatesByPrune_all_unbound (candidates : List Nat) :
    filterCandidatesByPrune candidates none none none none none none none
      = candidates := by
  simp [filterCandidatesByPrune, rgCanMatch_all_unbound]

/-! ## Build-time checks -/

private def pb : ByteArray := mkPresence 3 6 [(0, 1), (0, 4), (1, 2), (2, 3)]
private def hp : BitmapHandle := (openBitmapBytes pb).getD ⟨ByteArray.empty, default⟩

/-- Row group 0 holds predicates 1 and 3, and objects 2 and 4, but the
    only PAIRS it holds are `(1, 2)` and `(3, 4)`. -/
private def cb : ByteArray := mkCompound 6 6 [[(1, 2), (3, 4)], [], [(2, 2)]]
private def hc : CompoundHandle := (openCompoundBytes cb).getD ⟨ByteArray.empty, default⟩

private def po : ByteArray := mkPresence 3 6 [(0, 1), (0, 3), (1, 2), (2, 2)]
private def hpp : BitmapHandle := (openBitmapBytes po).getD ⟨ByteArray.empty, default⟩

/-! ### The per-column gates -/

#guard predicateCanMatch (some hpp) 0 (some 1)
#guard !predicateCanMatch (some hpp) 0 (some 5)
#guard predicateCanMatch (some hpp) 0 none          -- unbound: no opinion
#guard predicateCanMatch none 0 (some 5)            -- no companion: no opinion

/-! ### The compound gate is STRICTLY more selective

Row group 0 holds predicate 1 and object 4 individually, so every
per-column gate passes `(p=1, o=4)`. The compound gate rejects it,
because that pair is not in the same row. This is the reason the
compound bitmap exists, and a port that dropped the compound conjunct
would pass every per-column check while losing the whole benefit. -/

#guard predicateCanMatch (some hpp) 0 (some 1)      -- predicate present
#guard objectCanMatch (some hp) 0 (some 4)          -- object present
#guard !compoundPoCanMatch (some hc) 0 (some 1) (some 4)   -- but not together

#guard !rgCanMatch 0 none none (some hpp) (some 1) (some hp) (some 4) (some hc)
#guard rgCanMatch 0 none none (some hpp) (some 1) (some hp) (some 4) none
        -- ^ without the compound handle the same query is NOT ruled out

/-! A pair that IS stored together passes every gate. -/

#guard rgCanMatch 0 none none (some hpp) (some 1) (some hp) (some 1) (some hc)
        == (rgCouldContain (some hp) 0 (some 1) &&
            compoundPoCanMatch (some hc) 0 (some 1) (some 1))

/-! ### A decisive per-column `false` rules the row group out on its own -/

#guard !rgCanMatch 0 (some hp) (some 0) none none none none none
#guard rgCanMatch 0 (some hp) (some 1) none none none none none

/-! ### The filter preserves order and drops only ruled-out groups -/

#guard filterCandidatesByPrune [0, 1, 2] (some hp) (some 3) none none none none none
        == [2]
#guard filterCandidatesByPrune [2, 1, 0] (some hp) (some 3) none none none none none
        == [2]
#guard filterCandidatesByPrune [] (some hp) (some 3) none none none none none == []

/-! ### Turning the optimisation off changes nothing

The theorem says it in general; this says it on a concrete list, which
is what a caller sees. -/

#guard filterCandidatesByPrune [0, 1, 2, 7] none none none none none none none
        == [0, 1, 2, 7]

#print axioms rgCanMatch_all_unbound
#print axioms filterCandidatesByPrune_all_unbound

end L4Factoidal.Cottas
