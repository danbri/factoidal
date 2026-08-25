/-
L4Factoidal.Cottas.LazyTermCache — the two-direction term-id cache.

Port of `formal/fstar/RDF.Store.LazyTermCache.fst` (83 lines). Six
`assume val`s and one abstract type become none.

## What it is, and how it differs from `LazyDict`

Two indexed views over a backend's term inventory, populated together
on the first lookup:

| Direction | From | To |
|---|---|---|
| forward | id | typed value |
| reverse | canonical key | id |

`LazyDict` has FOUR directions because the COTTAS on-disk runtime needs
raw parquet column tokens beside typed values. HDT needs two: its
Front-Coded dictionary IS the canonical form, so there is no separate
raw view. That is the F\* module's own account of the difference.

## Status in the F\* tree: unused

The F\* header records this. Issue #253 was scoped to replace
`ballyhoo_hdt_runtime.sh`'s hand-written term-id allocator, and closed
a different way on 2026-07-06: that patch is deleted and
`Parser.BallyhooHDT` calls the verified `HDT.Container` /
`HDT.Dictionary` / `HDT.Triples` readers directly, with no cache in the
path. The module remains as a candidate memoisation seam for a
later performance pass, or for removal if that pass finds it
unneeded. The port carries the same status: nothing in the Lean tree
uses it either.

## `size` does not populate, and `LazyDict.size` does

The F\* comments differ and the port follows each. Here: "Number of
entries. 0 before populate; fixed positive nat after" — so `size` is a
pure observation and answers `0` on an unpopulated cache. In `LazyDict`
no such note appears and `size` goes through `ensure`. Two functions
with the same name and different triggering behaviour is a trap, so it
is written down in both modules rather than left to be discovered.

## The shape, as in `LazyDict`

Everything except one `IO.Ref` is pure, so the `#guard`s below cover
the cache's whole meaning and what they do not cover is exactly the
ref.
-/
import Std.Data.HashMap
import L4Factoidal.Cottas.LazyDict

namespace L4Factoidal.Cottas

/-- One entry: id and typed value. The populate thunk returns the full
    list, normally in id order. -/
abbrev TermEntries (α : Type) := List (Nat × α)

structure LoadedTermCache (α : Type) where
  byId   : Std.HashMap Nat α
  idByKey : Std.HashMap String Nat
  values : List α

/-- `keyOf` canonicalises values for the reverse direction. It exists
    in F\* to sidestep the `eqtype` constraint so values may be `noeq`
    — `RDF.Graph.Executable`'s `subject` is the case named there. Lean
    has no such constraint; the function is kept because the canonical
    key is a real part of the interface, not a workaround. -/
def buildTermCache {α : Type} (keyOf : α → String) (entries : TermEntries α) :
    LoadedTermCache α :=
  entries.foldl (fun acc (i, v) =>
      { byId := acc.byId.insert i v
      , idByKey := acc.idByKey.insert (keyOf v) i
      , values := acc.values })
    { byId := ∅, idByKey := ∅, values := entries.map (·.2) }

def LoadedTermCache.lookupById {α : Type} (c : LoadedTermCache α) (i : Nat) :
    Option α := c.byId[i]?

def LoadedTermCache.lookupByKey {α : Type} (c : LoadedTermCache α) (k : String) :
    Option Nat := c.idByKey[k]?

def LoadedTermCache.size {α : Type} (c : LoadedTermCache α) : Nat :=
  c.values.length

structure LazyTermCache (α : Type) where
  populate : IO (TermEntries α)
  keyOf    : α → String
  state    : IO.Ref (Option (LoadedTermCache α))

def mkLazyTermCache {α : Type} (populate : IO (TermEntries α))
    (keyOf : α → String) : IO (LazyTermCache α) := do
  return { populate := populate, keyOf := keyOf, state := ← IO.mkRef none }

def LazyTermCache.ensure {α : Type} (c : LazyTermCache α) :
    IO (LoadedTermCache α) := do
  match ← c.state.get with
  | some loaded => return loaded
  | none =>
      let loaded := buildTermCache c.keyOf (← c.populate)
      c.state.set (some loaded)
      return loaded

def LazyTermCache.lookupById {α : Type} (c : LazyTermCache α) (i : Nat) :
    IO (Option α) := return (← c.ensure).lookupById i

def LazyTermCache.lookupByKey {α : Type} (c : LazyTermCache α) (k : String) :
    IO (Option Nat) := return (← c.ensure).lookupByKey k

def LazyTermCache.isPopulated {α : Type} (c : LazyTermCache α) : IO Bool :=
  return (← c.state.get).isSome

/-- `0` before populate, the entry count after. This does NOT trigger
    the populate — see the module header, and contrast
    `LazyDict.size`, which does. -/
def LazyTermCache.size {α : Type} (c : LazyTermCache α) : IO Nat :=
  return match ← c.state.get with
         | none        => 0
         | some loaded => loaded.size

/-- The id-ordered typed values. Triggers the populate. -/
def LazyTermCache.toList {α : Type} (c : LazyTermCache α) : IO (List α) :=
  return (← c.ensure).values

/-! ## Build-time checks

Everything except the `IO.Ref` is pure and is checked here. What is NOT
checked: that `ensure` populates once and reuses, that `isPopulated`
does not populate, and that `size` answers `0` before it. Those need
`IO`. -/

private def tcFixture : TermEntries String :=
  [(0, "Alice"), (1, "Bob"), (2, "Carol")]

private def T : LoadedTermCache String := buildTermCache (·.toLower) tcFixture

#guard T.lookupById 1 == some "Bob"
#guard T.lookupByKey "bob" == some 1
#guard (T.lookupById 3).isNone
#guard (T.lookupByKey "dave").isNone
#guard T.size == 3
#guard T.values == ["Alice", "Bob", "Carol"]

/-! The reverse direction goes through `keyOf`, so the typed value's own
    spelling is not a key. -/

#guard (T.lookupByKey "Bob").isNone

/-! The two directions compose back to the identity on ids that are
    present, which is the property a caller resolving a term to an id
    and back relies on. -/

#guard (List.range 3).all (fun i =>
  match T.lookupById i with
  | some v => T.lookupByKey ((·.toLower) v) == some i
  | none   => false)

/-! Empty inventory. -/

#guard (buildTermCache (·.toLower) ([] : TermEntries String)).size == 0
#guard ((buildTermCache (·.toLower) ([] : TermEntries String)).lookupById 0).isNone

/-! Two values with the same canonical key: the LAST wins, as in
    `LazyDict`. HDT dictionaries hold distinct terms, so this should
    not arise; it is pinned rather than left to be discovered. -/

#guard (buildTermCache (·.toLower) [(0, "Bob"), (5, "BOB")]).lookupByKey "bob"
       == some 5
#guard (buildTermCache (·.toLower) [(0, "Bob"), (5, "BOB")]).lookupById 0
       == some "Bob"

end L4Factoidal.Cottas
