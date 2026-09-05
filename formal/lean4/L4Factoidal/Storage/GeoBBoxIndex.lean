/-
L4Factoidal.Storage.GeoBBoxIndex — the meaning of the GBI1 geometry
bounding-box index.

Design record: `docs/designissues/2026-09-05-geometry-bounding-box-index.md`.

A geo `FILTER` is a full scan today: every row is decoded, every
`geo:wktLiteral` lexical form is parsed into a `Geometry`, and the topology
algorithm runs on it. The parse is the expensive part and the scan pays it for
every row, answering or not.

This module indexes the axis-aligned bounding box of each `geo:wktLiteral`
term in the block dictionary, and the index is a CANDIDATE FILTER: it returns a
superset of the terms the filter accepts, and the caller re-evaluates the
original, unmodified SPARQL expression on the candidates.

## A box can exclude. A box can never confirm.

Two boxes that do not overlap prove the geometries share no point. Two boxes
that DO overlap prove nothing. Reading that backwards returns rows the query
does not license, so the direction is fixed here and proved:

* `mem_candidatesSpec` — a dictionary term the exact predicate accepts is
  always a candidate.
* `exists_common_point` — the geometric content, five predicates at a time.

`geof:sfDisjoint` is NOT served. It accepts exactly the rows a box can
exclude, so a box test inverts there; section 4.1 of the design record has the
argument. `candidatesSpec` returns `none` for it and the caller scans.

## The proved fragment

`fragmentBox` gives a box to a point, and to a polygon whose rings are all
closed. Every other geometry — a linestring, an empty, a `Multi*`, a
`GeometryCollection`, a polygon with an open ring — is OPAQUE: it carries no
box, it is always a candidate, and it costs the caller a re-evaluation it
would have paid anyway. The open obligation is the four-orientation
proper-crossing rule, which `segmentsIntersect` uses with no `inSegBBox`
conjunct and which needs the separating-axis argument; until that is proved,
linestrings stay opaque rather than being filtered on an unproved basis.

A term that is not a `geo:wktLiteral`, or whose lexical form does not parse,
is never a candidate: `Geo.geoPredicate` answers `none` for it, a `none` is a
§17.6 type error, and an error drops the row.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import Std.Data.HashMap
import L4Factoidal.Geo.BBoxSound
import L4Factoidal.Geo.Functions

namespace L4Factoidal.Storage.GeoBBoxIndex

open L4Factoidal.RDF
open L4Factoidal.Geo

/-! ## 1. The five served operations, and the one that is not -/

/-- The six GeoSPARQL topology functions the evaluator dispatches. -/
inductive GeoOp where
  | equals | within | contains | intersects | touches | disjoint
  deriving DecidableEq, Repr, Inhabited

/-- The predicate each name denotes. These ARE `Geo.sfEquals` and its
siblings; nothing is restated. -/
def GeoOp.fn : GeoOp → (Geometry → Geometry → Option Bool)
  | .equals     => sfEquals
  | .within     => sfWithin
  | .contains   => sfContains
  | .intersects => sfIntersects
  | .touches    => sfTouches
  | .disjoint   => sfDisjoint

/-- The local part of the `geof:` IRI. -/
def GeoOp.localName : GeoOp → String
  | .equals => "sfEquals" | .within => "sfWithin" | .contains => "sfContains"
  | .intersects => "sfIntersects" | .touches => "sfTouches" | .disjoint => "sfDisjoint"

/-- Parse the WKT out of a dictionary term. This is `Geo.wktArg` applied to
`EvalResult.term`, with the same datatype gate. -/
def termWkt (t : Term) : Option WktValue :=
  match t with
  | .literal l =>
      if l.val.datatype.val == wktLiteralIri then Wkt.parseLiteral l.val.lexicalForm
      else none
  | _ => none

/-- The exact predicate a row is judged by: the WKT gate, the CRS guard, then
the topology function. This is what `Geo.geoPredicate` computes; the `#guard`s
at the end of the module pin the two together through `Geo.extFns`. -/
def evalTerm (op : GeoOp) (t : Term) (query : WktValue) : Option Bool :=
  match termWkt t with
  | none => none
  | some v => if sameCrs v.crs query.crs then op.fn v.geom query.geom else none

/-! ## 2. The fragment the box covers -/

def ringsClosed (rs : List Ring) : Bool := rs.all isClosedLine

/-- The box of a geometry the soundness proof reaches: a point, or a polygon
whose exterior ring and holes are all closed. Anything else has no box and is
therefore always a candidate. -/
def fragmentBox : Geometry → Option BBox
  | .point p => some (BBox.ofPoint p)
  | .polygon poly =>
      if ringsClosed (poly.ext :: poly.holes) then BBox.ofRings (poly.ext :: poly.holes)
      else none
  | _ => none

/-- What the index knows about one dictionary term. -/
inductive TermGeo where
  /-- Not a parseable `geo:wktLiteral`. The evaluator refuses it, so it is
  never a candidate. -/
  | notGeo
  /-- A geometry outside the proved fragment. Always a candidate. -/
  | opaque
  /-- A geometry with a box, in the CRS recorded beside it. -/
  | boxed (crs : Option String) (box : BBox)
  deriving DecidableEq, Repr, Inhabited

def classify (t : Term) : TermGeo :=
  match termWkt t with
  | none => .notGeo
  | some v =>
      match fragmentBox v.geom with
      | some b => .boxed v.crs b
      | none => .opaque

/-- The candidate test. A boxed term survives only when its CRS matches the
query's — a cross-CRS pair is a type error the evaluator refuses, so excluding
it is free — and its box overlaps the query box. -/
def isCandidate (query : WktValue) (qbox : BBox) : TermGeo → Bool
  | .notGeo => false
  | .opaque => true
  | .boxed crs b => sameCrs crs query.crs && b.overlaps qbox

/-! ## 3. Five predicates, one shared point

The geometric content of the whole index. When a served predicate answers
`some true` on two geometries of the fragment, the two boxes contain a common
point, so a non-overlapping pair can never answer. -/

theorem Point_eq_symm {p q : Point} (h : Point.eq p q = true) : Point.eq q p = true := by
  simp only [Point.eq, Bool.and_eq_true] at h ⊢
  obtain ⟨hx, hy⟩ := h
  obtain ⟨hx1, hx2⟩ := Scaled.eq_le hx
  obtain ⟨hy1, hy2⟩ := Scaled.eq_le hy
  refine ⟨?_, ?_⟩
  · unfold Scaled.eq at hx ⊢
    simp only [beq_iff_eq] at hx ⊢
    rw [Scaled.cmp_swap p.x q.x, hx]; simp
  · unfold Scaled.eq at hy ⊢
    simp only [beq_iff_eq] at hy ⊢
    rw [Scaled.cmp_swap p.y q.y, hy]; simp

/-- A point lies in the box of any point equal to it. -/
theorem ofPoint_contains_eq {p q : Point} (h : Point.eq p q = true) :
    (BBox.ofPoint q).contains p = true := by
  simp only [Point.eq, Bool.and_eq_true] at h
  obtain ⟨hx1, hx2⟩ := Scaled.eq_le h.1
  obtain ⟨hy1, hy2⟩ := Scaled.eq_le h.2
  simp only [BBox.ofPoint, BBox.contains, Bool.and_eq_true]
  exact ⟨⟨⟨hx2, hx1⟩, hy2⟩, hy1⟩

/-- A polygon of the fragment: its box covers every ring, and its exterior
ring is closed. -/
theorem fragmentBox_polygon {poly : Polygon} {b : BBox}
    (h : fragmentBox (.polygon poly) = some b) :
    (∀ r ∈ poly.ext :: poly.holes, b.covers r) ∧ isClosedLine poly.ext = true := by
  simp only [fragmentBox] at h
  by_cases hc : ringsClosed (poly.ext :: poly.holes) = true
  · rw [if_pos hc] at h
    refine ⟨fun r hr q hq => BBox.ofRings_covers h r hr q hq, ?_⟩
    simp only [ringsClosed, List.all_eq_true] at hc
    exact hc poly.ext (by simp)
  · simp only [Bool.not_eq_true] at hc
    rw [if_neg (by simp [hc])] at h
    simp at h

/-- A point the polygon test calls non-exterior is inside the polygon's
fragment box. -/
theorem polygon_contains_of_ne_exterior {p : Point} {poly : Polygon} {b : BBox}
    (hb : fragmentBox (.polygon poly) = some b)
    (h : polygonClass p poly ≠ PtClass.exterior) : b.contains p = true := by
  obtain ⟨hcov, hclosed⟩ := fragmentBox_polygon hb
  exact polygonClass_ne_exterior_contains hcov hclosed h

theorem interior_ne_exterior {p : Point} {poly : Polygon}
    (h : (polygonClass p poly == PtClass.interior) = true) :
    polygonClass p poly ≠ PtClass.exterior := by
  simp only [beq_iff_eq] at h
  rw [h]; simp

theorem boundary_ne_exterior {p : Point} {poly : Polygon}
    (h : (polygonClass p poly == PtClass.boundary) = true) :
    polygonClass p poly ≠ PtClass.exterior := by
  simp only [beq_iff_eq] at h
  rw [h]; simp

theorem ne_exterior_of_bne {p : Point} {poly : Polygon}
    (h : (polygonClass p poly != PtClass.exterior) = true) :
    polygonClass p poly ≠ PtClass.exterior := by
  simp only [bne_iff_ne, ne_eq] at h
  exact h

/-- **The geometric core.** Two fragment geometries a served predicate accepts
have a point that both boxes contain. `sfDisjoint` is excluded: it is the one
predicate whose truth is the ABSENCE of a shared point. -/
theorem exists_common_point {op : GeoOp} (hop : op ≠ GeoOp.disjoint)
    {g q : Geometry} {bg bq : BBox}
    (hg : fragmentBox g = some bg) (hq : fragmentBox q = some bq)
    (h : op.fn g q = some true) :
    ∃ r, bg.contains r = true ∧ bq.contains r = true := by
  -- `fragmentBox` is `some` only for a point or a polygon, and neither is
  -- compound, so every `sfX` below reduces to its base case.
  match hgg : g, hqq : q with
  | .point p1, .point p2 =>
      simp only [fragmentBox, Option.some.injEq] at hg hq
      subst hg; subst hq
      refine ⟨p1, contains_ofPoint p1, ?_⟩
      cases op with
      | disjoint => exact absurd rfl hop
      | equals =>
          simp only [GeoOp.fn, sfEquals, isCompound, sfEqualsBase, Option.some.injEq] at h
          exact ofPoint_contains_eq (by simpa using h)
      | within =>
          simp only [GeoOp.fn, sfWithin, isCompound, sfWithinBase, Option.some.injEq] at h
          exact ofPoint_contains_eq (by simpa using h)
      | intersects =>
          simp only [GeoOp.fn, sfIntersects, isCompound, sfIntersectsBase,
            Option.some.injEq] at h
          exact ofPoint_contains_eq (by simpa using h)
      | contains =>
          simp only [GeoOp.fn, sfContains, sfWithin, isCompound, sfWithinBase,
            Option.some.injEq] at h
          exact ofPoint_contains_eq (Point_eq_symm (by simpa using h))
      | touches =>
          simp only [GeoOp.fn, sfTouches, isCompound, sfTouchesBase] at h
          simp at h
  | .point p, .polygon poly =>
      simp only [fragmentBox, Option.some.injEq] at hg
      subst hg
      refine ⟨p, contains_ofPoint p, ?_⟩
      cases op with
      | disjoint => exact absurd rfl hop
      | equals =>
          simp only [GeoOp.fn, sfEquals, isCompound, sfEqualsBase] at h
          simp at h
      | contains =>
          simp only [GeoOp.fn, sfContains, sfWithin, isCompound, sfWithinBase] at h
          simp at h
      | within =>
          simp only [GeoOp.fn, sfWithin, isCompound, sfWithinBase, Option.some.injEq] at h
          exact polygon_contains_of_ne_exterior hq (interior_ne_exterior (by simpa using h))
      | intersects =>
          simp only [GeoOp.fn, sfIntersects, isCompound, sfIntersectsBase,
            Option.some.injEq] at h
          exact polygon_contains_of_ne_exterior hq (ne_exterior_of_bne (by simpa using h))
      | touches =>
          simp only [GeoOp.fn, sfTouches, isCompound, sfTouchesBase, Option.some.injEq] at h
          exact polygon_contains_of_ne_exterior hq (boundary_ne_exterior (by simpa using h))
  | .polygon poly, .point p =>
      simp only [fragmentBox, Option.some.injEq] at hq
      subst hq
      refine ⟨p, ?_, contains_ofPoint p⟩
      cases op with
      | disjoint => exact absurd rfl hop
      | equals =>
          simp only [GeoOp.fn, sfEquals, isCompound, sfEqualsBase] at h
          simp at h
      | within =>
          simp only [GeoOp.fn, sfWithin, isCompound, sfWithinBase] at h
          simp at h
      | contains =>
          simp only [GeoOp.fn, sfContains, sfWithin, isCompound, sfWithinBase,
            Option.some.injEq] at h
          exact polygon_contains_of_ne_exterior hg (interior_ne_exterior (by simpa using h))
      | intersects =>
          simp only [GeoOp.fn, sfIntersects, isCompound, sfIntersectsBase,
            Option.some.injEq] at h
          exact polygon_contains_of_ne_exterior hg (ne_exterior_of_bne (by simpa using h))
      | touches =>
          simp only [GeoOp.fn, sfTouches, isCompound, sfTouchesBase, Option.some.injEq] at h
          exact polygon_contains_of_ne_exterior hg (boundary_ne_exterior (by simpa using h))
  | .polygon poly1, .polygon poly2 =>
      -- Every base predicate REFUSES a polygon pair, so no row is accepted.
      exfalso
      cases op with
      | disjoint => exact absurd rfl hop
      | equals => simp [GeoOp.fn, sfEquals, isCompound, sfEqualsBase] at h
      | within => simp [GeoOp.fn, sfWithin, isCompound, sfWithinBase] at h
      | contains => simp [GeoOp.fn, sfContains, sfWithin, isCompound, sfWithinBase] at h
      | intersects => simp [GeoOp.fn, sfIntersects, isCompound, sfIntersectsBase] at h
      | touches => simp [GeoOp.fn, sfTouches, isCompound, sfTouchesBase] at h
  | .point _, .lineString _ | .point _, .multiPoint _ | .point _, .multiLineString _
  | .point _, .multiPolygon _ | .point _, .geometryCollection _ | .point _, .empty _
  | .polygon _, .lineString _ | .polygon _, .multiPoint _ | .polygon _, .multiLineString _
  | .polygon _, .multiPolygon _ | .polygon _, .geometryCollection _ | .polygon _, .empty _ =>
      simp [fragmentBox] at hq
  | .lineString _, _ | .multiPoint _, _ | .multiLineString _, _
  | .multiPolygon _, _ | .geometryCollection _, _ | .empty _, _ =>
      simp [fragmentBox] at hg

/-- Every served predicate that accepts a fragment term makes the boxes
overlap. This is `exists_common_point` composed with
`BBox.overlaps_of_common_point`. -/
theorem overlaps_of_accept {op : GeoOp} (hop : op ≠ GeoOp.disjoint)
    {g q : Geometry} {bg bq : BBox}
    (hg : fragmentBox g = some bg) (hq : fragmentBox q = some bq)
    (h : op.fn g q = some true) : bg.overlaps bq = true := by
  obtain ⟨r, h1, h2⟩ := exists_common_point hop hg hq h
  exact BBox.overlaps_of_common_point h1 h2

/-- The per-term soundness step: a term the exact predicate accepts passes the
candidate test. -/
theorem isCandidate_of_evalTerm {op : GeoOp} (hop : op ≠ GeoOp.disjoint)
    {t : Term} {query : WktValue} {qbox : BBox}
    (hq : fragmentBox query.geom = some qbox)
    (h : evalTerm op t query = some true) :
    isCandidate query qbox (classify t) = true := by
  unfold evalTerm at h
  unfold classify
  cases hw : termWkt t with
  | none => rw [hw] at h; simp at h
  | some v =>
      simp only [hw] at h
      by_cases hcrs : sameCrs v.crs query.crs = true
      · simp only [hcrs, if_true] at h
        cases hb : fragmentBox v.geom with
        | none => simp [hb, isCandidate]
        | some bv =>
            simp only [hb, isCandidate, Bool.and_eq_true]
            exact ⟨hcrs, overlaps_of_accept hop hb hq h⟩
      · simp only [Bool.not_eq_true] at hcrs
        simp only [hcrs, Bool.false_eq_true, if_false] at h
        simp at h

/-! ## 4. The index specification and its candidate list -/

/-- The dictionary positions of a block, paired with what the index knows
about each term. The position is the PTD1 local ID, the identity TLI1 and
LGI1 use. -/
def withIds : Nat → List Term → List (Nat × TermGeo)
  | _, [] => []
  | i, t :: rest => (i, classify t) :: withIds (i + 1) rest

/-- The candidate local IDs, or `none` when the index cannot serve the query:
the operation is `sfDisjoint`, or the query geometry is outside the fragment
and has no box. -/
def candidatesSpec (dict : Array Term) (op : GeoOp) (query : WktValue) :
    Option (List Nat) :=
  if op == GeoOp.disjoint then none
  else
    match fragmentBox query.geom with
    | none => none
    | some qbox =>
        some ((withIds 0 dict.toList).filterMap
          (fun pr => if isCandidate query qbox pr.2 then some pr.1 else none))

theorem mem_withIds :
    ∀ (l : List Term) (base i : Nat) (t : Term), l[i]? = some t →
      (base + i, classify t) ∈ withIds base l := by
  intro l
  induction l with
  | nil => intro base i t h; simp at h
  | cons x xs ih =>
      intro base i t h
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h
          subst h
          simp [withIds]
      | succ i =>
          simp only [List.getElem?_cons_succ] at h
          have := ih (base + 1) i t h
          simp only [withIds, List.mem_cons]
          refine Or.inr ?_
          have hb : base + (i + 1) = base + 1 + i := by omega
          rw [hb]
          exact this

/-- **The soundness gate.** A dictionary term the exact GeoSPARQL predicate
accepts is in the candidate list. The caller then re-evaluates that same
expression on the candidates, so its rows are the rows a full scan returns. -/
theorem mem_candidatesSpec (dict : Array Term) (op : GeoOp) (query : WktValue)
    (i : Nat) (t : Term) (ids : List Nat)
    (hop : op ≠ GeoOp.disjoint)
    (hget : dict.toList[i]? = some t)
    (hmatch : evalTerm op t query = some true)
    (hc : candidatesSpec dict op query = some ids) :
    i ∈ ids := by
  unfold candidatesSpec at hc
  rw [if_neg (by simp [hop])] at hc
  cases hq : fragmentBox query.geom with
  | none => rw [hq] at hc; simp at hc
  | some qbox =>
      rw [hq] at hc
      simp only [Option.some.injEq] at hc
      subst hc
      have hmem : (0 + i, classify t) ∈ withIds 0 dict.toList :=
        mem_withIds dict.toList 0 i t hget
      simp only [Nat.zero_add] at hmem
      simp only [List.mem_filterMap]
      exact ⟨(i, classify t), hmem, by simp [isCandidate_of_evalTerm hop hq hmatch]⟩

/-! ## 5. The runtime index

The specification above filters the whole dictionary. The artifact stores one
fixed-size entry per BOXED term, ascending by local ID, plus the ascending IDs
of the OPAQUE terms — the geometries outside the fragment, which are always
candidates and therefore cannot be dropped from the answer. A term that is not
a parseable `geo:wktLiteral` appears in neither list, because it can never be
a candidate.

`agreesWithSpec` is the contract between the two. -/

structure Entry where
  id : Nat
  /-- 0 means the default CRS84; otherwise a 1-based index into `crsTable`. -/
  crsIndex : Nat
  box : BBox
  deriving DecidableEq, Repr, Inhabited

structure Index where
  /-- The block dictionary size. Every ID is below it. -/
  dictCount : Nat
  crsTable : Array String
  entries : Array Entry
  /-- Parseable geometries outside the proved fragment, ascending. Always
  candidates. -/
  opaqueIds : Array Nat
  deriving DecidableEq, Repr, Inhabited

/-- The CRS an entry names, or `none` when the table cannot resolve it. -/
def resolveCrs (idx : Index) (e : Entry) : Option (Option String) :=
  if e.crsIndex == 0 then some none
  else match idx.crsTable[e.crsIndex - 1]? with
    | some c => some (some c)
    | none => none

/-- The runtime candidate test for one entry. An unresolvable CRS index means
a malformed table, and the entry is kept rather than dropped. -/
def entryCandidate (idx : Index) (query : WktValue) (qbox : BBox) (e : Entry) : Bool :=
  match resolveCrs idx e with
  | none => true
  | some crs => sameCrs crs query.crs && e.box.overlaps qbox

/-- Merge two ascending ID lists into one ascending list without duplicates.
`fuel` is one more than the combined length, so the exhausted case is
unreachable. -/
private def mergeGo : Nat → List Nat → List Nat → List Nat → List Nat
  | 0, _, _, acc => acc.reverse
  | _ + 1, [], ys, acc => acc.reverse ++ ys
  | _ + 1, xs, [], acc => acc.reverse ++ xs
  | fuel + 1, x :: xs, y :: ys, acc =>
      if x == y then mergeGo fuel xs ys (x :: acc)
      else if x < y then mergeGo fuel xs (y :: ys) (x :: acc)
      else mergeGo fuel (x :: xs) ys (y :: acc)

def mergeAscending (xs ys : List Nat) : List Nat :=
  mergeGo (xs.length + ys.length + 1) xs ys []

/-- The runtime form of `candidatesSpec`. -/
def candidates? (idx : Index) (op : GeoOp) (query : WktValue) : Option (List Nat) :=
  if op == GeoOp.disjoint then none
  else
    match fragmentBox query.geom with
    | none => none
    | some qbox =>
        let passing := idx.entries.toList.filterMap (fun e =>
          if entryCandidate idx query qbox e then some e.id else none)
        some (mergeAscending passing idx.opaqueIds.toList)

/-! ### Building the index from a block dictionary -/

private def crsSlotOf (table : Array String) (crs : Option String) : Array String × Nat :=
  match crs with
  | none => (table, 0)
  | some c =>
      match table.findIdx? (fun s => s == c) with
      | some k => (table, k + 1)
      | none => (table.push c, table.size + 1)

/-- Build the index of one block dictionary. Terms are visited in dictionary
order, so both ID lists are ascending by construction. -/
def build (dict : Array Term) : Index := Id.run do
  let mut table : Array String := #[]
  let mut entries : Array Entry := #[]
  let mut opaqueIds : Array Nat := #[]
  for h : i in [0 : dict.size] do
    match classify dict[i] with
    | .notGeo => pure ()
    | .opaque => opaqueIds := opaqueIds.push i
    | .boxed crs box =>
        let (table', slot) := crsSlotOf table crs
        table := table'
        entries := entries.push { id := i, crsIndex := slot, box := box }
  pure { dictCount := dict.size, crsTable := table, entries := entries,
         opaqueIds := opaqueIds }

/-- The contract between the stored index and the specification. -/
def agreesWithSpec (dict : Array Term) (op : GeoOp) (query : WktValue) : Bool :=
  candidates? (build dict) op query == candidatesSpec dict op query

/-! ## 6. Samples

The `extFns` guards pin `evalTerm` to what the evaluator actually computes:
the same WKT gate, the same CRS guard, the same topology function. If
`Geo.geoPredicate` changes, these fail. -/

private def wkt (s : String) : Term :=
  .literal ⟨⟨s, ⟨wktLiteralIri, by rfl⟩, none, none⟩, by rfl⟩
private def ex : WfIri := ⟨"https://example.test/a", by decide⟩
private def plain (s : String) : Term :=
  .literal ⟨⟨s, ⟨"http://www.w3.org/2001/XMLSchema#string", by rfl⟩, none, none⟩, by rfl⟩

/-- A unit square from (0,0) to (10,10). -/
private def squareWkt : String := "POLYGON((0 0, 10 0, 10 10, 0 10, 0 0))"
private def square : WktValue := (Wkt.parseLiteral squareWkt).getD ⟨none, .empty .polygon⟩
/-- A square far away, over empty space. -/
private def elsewhereWkt : String := "POLYGON((900 900, 910 900, 910 910, 900 910, 900 900))"
private def elsewhere : WktValue :=
  (Wkt.parseLiteral elsewhereWkt).getD ⟨none, .empty .polygon⟩

private def sampleDict : Array Term :=
  #[wkt "POINT(1 1)",                    -- inside the square
    wkt "POINT(5 5)",                    -- inside the square
    wkt "POINT(50 50)",                  -- outside every query box
    wkt "LINESTRING(0 0, 1 1)",          -- outside the fragment: opaque
    .iri ex,                             -- not a geometry
    plain "not a geometry",              -- not a geometry
    wkt "POINT(0 0)"]                    -- on the square's boundary

#guard (fragmentBox square.geom).isSome
#guard classify (wkt "POINT(1 1)") != TermGeo.notGeo
#guard classify (.iri ex) == TermGeo.notGeo
#guard classify (plain "x") == TermGeo.notGeo
#guard classify (wkt "LINESTRING(0 0, 1 1)") == TermGeo.opaque
#guard classify (wkt "POINT(nonsense)") == TermGeo.notGeo

-- `sfWithin` against the square: the two interior points, plus the opaque
-- linestring which the caller re-checks. The boundary point (0 0) is NOT
-- within by Simple Features, but it IS a candidate: the box may not decide.
#guard candidatesSpec sampleDict GeoOp.within square == some [0, 1, 3, 6]
-- The MISS: a query over empty space keeps only the opaque term.
#guard candidatesSpec sampleDict GeoOp.within elsewhere == some [3]
#guard candidatesSpec sampleDict GeoOp.intersects elsewhere == some [3]
-- `sfDisjoint` is refused; the caller scans.
#guard candidatesSpec sampleDict GeoOp.disjoint square == none
-- A query geometry outside the fragment is refused too.
#guard candidatesSpec sampleDict GeoOp.within
  ((Wkt.parseLiteral "LINESTRING(0 0, 1 1)").getD ⟨none, .empty .polygon⟩) == none

#guard agreesWithSpec sampleDict GeoOp.within square
#guard agreesWithSpec sampleDict GeoOp.within elsewhere
#guard agreesWithSpec sampleDict GeoOp.intersects square
#guard agreesWithSpec sampleDict GeoOp.touches square
#guard agreesWithSpec sampleDict GeoOp.equals square
#guard agreesWithSpec sampleDict GeoOp.contains square
#guard agreesWithSpec sampleDict GeoOp.disjoint square

#guard (build sampleDict).dictCount == 7
#guard (build sampleDict).entries.size == 4
#guard (build sampleDict).opaqueIds == #[3]

/-- The evaluator's own answer for the same pair, through `Geo.extFns`. -/
private def viaExtFns (op : GeoOp) (t : Term) (queryLexical : String) :
    Option SPARQL.EvalResult :=
  extFns (geofNs ++ op.localName)
    [SPARQL.EvalResult.term t, SPARQL.EvalResult.term (wkt queryLexical)]

/-- What `evalTerm` says, in the evaluator's own result shape. -/
private def viaEvalTerm (op : GeoOp) (t : Term) (query : WktValue) :
    Option SPARQL.EvalResult :=
  (evalTerm op t query).map SPARQL.EvalResult.bool

#guard viaExtFns GeoOp.within (wkt "POINT(1 1)") squareWkt
  == viaEvalTerm GeoOp.within (wkt "POINT(1 1)") square
#guard viaExtFns GeoOp.within (wkt "POINT(50 50)") squareWkt
  == viaEvalTerm GeoOp.within (wkt "POINT(50 50)") square
#guard viaExtFns GeoOp.intersects (wkt "POINT(0 0)") squareWkt
  == viaEvalTerm GeoOp.intersects (wkt "POINT(0 0)") square
#guard viaExtFns GeoOp.touches (wkt "POINT(0 0)") squareWkt
  == viaEvalTerm GeoOp.touches (wkt "POINT(0 0)") square
#guard viaExtFns GeoOp.disjoint (wkt "POINT(50 50)") squareWkt
  == viaEvalTerm GeoOp.disjoint (wkt "POINT(50 50)") square
#guard viaExtFns GeoOp.equals (wkt "POINT(1 1)") "POINT(1 1)"
  == viaEvalTerm GeoOp.equals (wkt "POINT(1 1)")
      ((Wkt.parseLiteral "POINT(1 1)").getD ⟨none, .empty .point⟩)
#guard viaExtFns GeoOp.contains (wkt squareWkt) "POINT(1 1)"
  == viaEvalTerm GeoOp.contains (wkt squareWkt)
      ((Wkt.parseLiteral "POINT(1 1)").getD ⟨none, .empty .point⟩)

#print axioms mem_candidatesSpec
#print axioms exists_common_point

end L4Factoidal.Storage.GeoBBoxIndex
