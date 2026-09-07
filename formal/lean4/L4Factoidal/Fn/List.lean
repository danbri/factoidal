/-
L4Factoidal.Fn.List — the RIF-DTB 4.11 list functions.

RIF lists are TERMS, not XPath sequences, so these are RIF-specific:
F&O's sequence functions (§15) are the model, but the correspondence
is by analogy and the specification does not cite them. They are
written here, polymorphic over any type with `BEq`, so a SPARQL or
XPath sequence layer can reuse them without a second copy.

An index is 0-BASED, and a NEGATIVE index counts from the end: `-1` is
the last element and `-n` the first of an `n`-element list. Every
function below normalises through `listIndex`, so the rule is stated
once.

`indexOf`, `union`, `distinctValues`, `intersect` and `except` all
preserve the order of their FIRST argument, which is the order the
Approved `Builtins_List` fixture writes their results in.
-/

namespace L4Factoidal.Fn.List

variable {α : Type} [BEq α]

/-- A DTB list index normalised to a position, or `none` when it is out
    of range. -/
def listIndex (len : Nat) (i : Int) : Option Nat :=
  let j := if i < 0 then Int.ofNat len + i else i
  if j < 0 || j ≥ Int.ofNat len then none else some j.toNat

/-- `func:distinct-values`, first occurrence wins. -/
def dedup (xs : List α) : List α :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- `func:get`. -/
def get? (xs : List α) (i : Int) : Option α :=
  (listIndex xs.length i).bind (fun j => xs[j]?)

/-- `func:sublist` with a start and an end, the end EXCLUSIVE. -/
def sublist? (xs : List α) (from_ to_ : Int) : Option (List α) :=
  match listIndex xs.length from_ with
  | none   => none
  | some a =>
      let n := xs.length
      let b := if to_ < 0 then Int.ofNat n + to_ else to_
      if b < Int.ofNat a || b > Int.ofNat n then none
      else some ((xs.drop a).take (b.toNat - a))

/-- `func:sublist` with a start only. -/
def sublistFrom? (xs : List α) (from_ : Int) : Option (List α) :=
  (listIndex xs.length from_).map (fun a => xs.drop a)

/-- `func:insert-before`. -/
def insertBefore? (xs : List α) (i : Int) (y : α) : Option (List α) :=
  (listIndex xs.length i).map (fun j => xs.take j ++ [y] ++ xs.drop j)

/-- `func:remove`. -/
def remove? (xs : List α) (i : Int) : Option (List α) :=
  (listIndex xs.length i).map (fun j => xs.take j ++ xs.drop (j + 1))

/-- `func:index-of`: every 0-based position at which `y` occurs. -/
def indexOf (xs : List α) (y : α) : List Nat :=
  (xs.zipIdx).filterMap (fun (x, i) => if x == y then some i else none)

/-- `func:union`, order-preserving and duplicate-free. -/
def union (xs ys : List α) : List α := dedup (xs ++ ys)

/-- `func:intersect`, in the order of the FIRST argument. -/
def intersect (xs ys : List α) : List α := (dedup xs).filter (fun x => ys.contains x)

/-- `func:except`. -/
def except (xs ys : List α) : List α := (dedup xs).filter (fun x => !ys.contains x)

/-! ## Pins, over `Nat` -/

private def l5 : List Nat := [0, 1, 2, 3, 4]

#guard get? l5 (-1) = some 4
#guard get? l5 5 = none
#guard sublist? l5 0 5 = some l5
#guard sublist? l5 1 3 = some [1, 2]
#guard insertBefore? l5 (-1) 99 = some [0, 1, 2, 3, 99, 4]
#guard remove? l5 (-5) = some [1, 2, 3, 4]
#guard indexOf [0, 1, 2, 3, 4, 5, 2, 2] 2 = [2, 6, 7]
#guard union [0, 1, 2, 3] [4] = l5
#guard dedup [3, 3, 3] = [3]
#guard intersect l5 [3, 1] = [1, 3]
#guard except l5 [1, 3] = [0, 2, 4]

/-- Every index `listIndex` accepts is a position of the list. This is
    what lets `get?`, `remove?` and `insertBefore?` use `List.take` and
    `List.drop` without a bound check of their own. -/
theorem listIndex_lt {len : Nat} {i : Int} {j : Nat} (h : listIndex len i = some j) :
    j < len := by
  unfold listIndex at h
  by_cases hc : i < 0
  · simp [hc] at h; omega
  · simp [hc] at h; omega

end L4Factoidal.Fn.List
